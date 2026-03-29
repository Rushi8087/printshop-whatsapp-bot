import os, io, uuid, json
from flask import Flask, request, jsonify, render_template, redirect, url_for
from flask_cors import CORS
import requests
from pathlib import Path
from PyPDF2 import PdfReader
from PIL import Image
from dotenv import load_dotenv
from datetime import datetime
from collections import defaultdict
import time
import math
from phonepe_payment import initiate_payment, verify_payment
import base64
from urllib.parse import urlparse, unquote
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from werkzeug.utils import secure_filename

load_dotenv()
BACKEND_API_URL = os.getenv('BACKEND_API_URL', 'http://localhost:5001')
NGROK_URL = os.getenv("NGROK_URL")
UPLOAD_DIR = Path("uploads")
ORDERS_DIR = Path("orders")
UPLOAD_DIR.mkdir(exist_ok=True)
ORDERS_DIR.mkdir(exist_ok=True)
PHONEPE_CALLBACK_URL = os.getenv("PHONEPE_CALLBACK_URL")
PHONEPE_REDIRECT_URL = os.getenv("PHONEPE_REDIRECT_URL")
NODEJS_BOT_URL = os.getenv('NODEJS_BOT_URL', 'http://localhost:3000')
# PROJECT_ROOT removed
TEMPLATE_DIR = Path(__file__).parent / "templates"
ORDERS_API_KEY = os.getenv('ORDERS_API_KEY')
app = Flask(__name__, template_folder=str(TEMPLATE_DIR))
CORS(app, resources={r"/*": {"origins": [
    "http://localhost:5001",
    "http://localhost:3000",
    os.getenv("NGROK_URL", "")  # allow your ngrok URL dynamically
]}})
app.config['MAX_CONTENT_LENGTH'] = 50 * 1024 * 1024  # 50MB max file size
sessions = {}
BOT_START_TIME = int(time.time())
print(f"🚀 Bot started at: {BOT_START_TIME} ({datetime.fromtimestamp(BOT_START_TIME)})")
payment_notifications_sent = set()
sessions_lock = threading.Lock()
SUPPORTED_FORMATS = {
    'pdf': ['pdf'],
    'image': ['jpg', 'jpeg', 'png', 'gif', 'bmp', 'webp', 'tiff', 'tif', 'heic', 'heif'],
    'document': ['doc', 'docx', 'txt', 'rtf', 'odt'],
    'spreadsheet': ['xls', 'xlsx', 'csv'],
    'presentation': ['ppt', 'pptx']
}

PRICING = {
    'sheet_bw': 1.1,
    'sheet_color': 6.0
}

pending_confirmations = defaultdict(lambda: {
    'files': [],
    'timer': None,
    'lock': threading.Lock()
})
verification_completed = {}
verification_in_progress = set()  # Track orders currently being verified

def cleanup_old_sessions():
    """Remove sessions older than 2 hours — runs every 30 minutes"""
    while True:
        try:
            time.sleep(1800)  # Wait 30 minutes between runs
            now = datetime.utcnow()
            to_delete = []

            # ── ISSUE 4 FIX: Use sessions_lock when reading/deleting sessions ──
            # Before fix: iterated and deleted sessions without lock
            # A webhook request mid-deletion would see corrupt state
            with sessions_lock:
                for phone, job in list(sessions.items()):
                    completed_at = job.get("completed_at")
                    if completed_at:
                        age = (now - datetime.fromisoformat(completed_at)).total_seconds()
                        if age > 7200:  # 2 hours
                            to_delete.append(phone)

                for phone in to_delete:
                    del sessions[phone]
                    print(f"🗑️ Cleaned up session for {phone}")

            print(f"🧹 Sessions cleanup: removed {len(to_delete)} old sessions")

            # ── ISSUE 7 FIX: Trim verification_completed dict ──
            # Before fix: grew forever — 1 entry per order, never deleted
            # After fix:  capped at 500 entries max
            if len(verification_completed) > 500:
                keys = list(verification_completed.keys())
                # Delete the oldest half (first 250 keys)
                for k in keys[:250]:
                    del verification_completed[k]
                print(f"🗑️ Trimmed verification_completed: removed 250 old entries")

            # Cap payment_notifications_sent set
            if len(payment_notifications_sent) > 1000:
                payment_notifications_sent.clear()
                print("🗑️ Cleared payment_notifications_sent set")

        except Exception as e:
            print(f"❌ Cleanup error: {e}")
            import traceback
            traceback.print_exc()
cleanup_thread = threading.Thread(target=cleanup_old_sessions, daemon=True)
cleanup_thread.start()
INTERNAL_API_KEY = os.getenv('INTERNAL_API_KEY')

def update_order_in_backend(order_id, payment_status, order_status, shop_id=None):
    try:
        response = requests.post(
            f"{BACKEND_API_URL}/api/public/order/submit",
            json={
                "order_id": order_id,
                "payment_status": payment_status,
                "order_status": order_status,
                "shop_id": shop_id
            },
            headers={"X-Internal-Key": INTERNAL_API_KEY},  # ← ADD THIS
            timeout=10
        )
        if response.ok:
            print(f"✅ Backend synced: {order_id} → {payment_status}/{order_status}")
        else:
            print(f"⚠️ Backend sync failed: {response.status_code} - {response.text}")
    except Exception as e:
        print(f"❌ Backend sync error: {e}")
def get_printer_config_for_shop(shop_id):
    """Fetch printer config from backend database"""
    try:
        response = requests.get(
            f"{BACKEND_API_URL}/api/public/shop-printer-config/{shop_id}",
            timeout=5
        )
        print(f"🔍 Printer config fetch for {shop_id}: {response.status_code} - {response.text[:100]}")  # ADD THIS
        if response.ok:
            return response.json().get('printer_config')
        return None
    except Exception as e:
        print(f"⚠️ Could not fetch printer config: {e}")
        return None
def get_shop_by_phone_number(phone):
    """Get shop info by WhatsApp phone number"""
    try:
        response = requests.get(
            f"{BACKEND_API_URL}/api/public/shop-by-phone/{phone}",
            timeout=5
        )
        if response.ok:
            return response.json()
        return None
    except Exception as e:
        print(f"⚠️ Error fetching shop by phone: {e}")
        return None


def reset_session(phone, delay_seconds=15):
    """
    Reset session for a new order.
    Preserves WhatsApp session and shop info.
    Delayed to allow payment status checks to complete first.
    """
    def delayed_reset():
        try:
            print(f"⏰ Waiting {delay_seconds}s before resetting session for {phone}...")
            time.sleep(delay_seconds)
            with sessions_lock:

                # Check if session still exists
                if phone not in sessions:
                    print(f"⚠️ Session for {phone} already removed, skipping reset")
                    return

                # Read old values while holding the lock
                old_whatsapp_session = sessions[phone].get("whatsapp_session_id")
                old_shop_id          = sessions[phone].get("shop_id")
                old_shop_db_id       = sessions[phone].get("shop_database_id")
                old_session_id       = sessions[phone].get("session_id", "unknown")

                # Create new session — overwrite atomically while still holding lock
                session_id = uuid.uuid4().hex[:12].upper()

                sessions[phone] = {
                    "session_id":         session_id,
                    "whatsapp_session_id": old_whatsapp_session,  # preserved
                    "shop_id":             old_shop_id,            # preserved
                    "shop_database_id":    old_shop_db_id,         # preserved
                    "order_placed":        False,
                    "order_data": {
                        "order_id":       f"ORD_{uuid.uuid4().hex[:8].upper()}",
                        "session_id":     session_id,
                        "user_id":        phone,
                        "timestamp":      datetime.utcnow().isoformat(),
                        "files":          [],
                        "total_price":    None,
                        "total_pages":    None,
                        "total_sheets":   None,
                        "payment_status": "pending",
                        "order_status":   "pending"
                    }
                }

            # Log outside the lock — logging can be slow
            print(f"✅ Session reset complete for {phone}")
            print(f"   Old session: {old_session_id}")
            print(f"   New session: {session_id}")
            print(f"   Preserved WhatsApp session: {old_whatsapp_session}")
            print(f"   Preserved Shop ID: {old_shop_id}")

        except Exception as e:
            print(f"❌ Error in delayed_reset for {phone}: {e}")
            import traceback
            traceback.print_exc()

    # ── Mark order as completed (outside lock — just setting two keys) ──
    # This is safe because we're only adding keys, not restructuring the dict
    with sessions_lock:
        if phone in sessions:
            sessions[phone]["order_completed"] = True
            sessions[phone]["completed_at"]    = datetime.utcnow().isoformat()
            print(f"🏁 Marked order as completed for {phone}, will reset in {delay_seconds}s")

    # Schedule the actual reset in background
    reset_thread = threading.Thread(target=delayed_reset, daemon=True)
    reset_thread.start()

    with sessions_lock:
        return sessions[phone].get("session_id") if phone in sessions else None

# ✅ NEW HELPER FUNCTION: Format price to 2 decimal places
def get_shop_by_whatsapp_session(session_id):
    """Get shop info from backend API by session ID"""
    try:
        response = requests.get(
            f"{BACKEND_API_URL}/api/public/shop-by-session/{session_id}",
            timeout=5
        )
        if response.ok:
            return response.json()
        return None
    except Exception as e:
        print(f"⚠️ Error fetching shop: {e}")
        return None
def format_price(price):
    return round(float(price), 2)
def prepare_file_for_printing(file_path):
    """Convert file to PDF for printing."""
    file_ext = file_path.rsplit('.', 1)[-1].lower() if '.' in file_path else ''

    # Images → PDF
    if file_ext in ['jpg', 'jpeg', 'png', 'bmp', 'webp', 'tiff', 'tif']:
        try:
            from PIL import Image
            print(f"🔄 Converting {file_ext.upper()} to PDF...")
            img = Image.open(file_path)
            if img.mode in ('RGBA', 'LA', 'P'):
                img = img.convert('RGB')
            img.thumbnail((2480, 3508), Image.LANCZOS)  # A4 at 300dpi
            pdf_path = file_path.rsplit('.', 1)[0] + '_print.pdf'
            img.save(pdf_path, 'PDF', resolution=300)
            print(f"✅ Converted to PDF: {pdf_path}")
            return pdf_path
        except Exception as e:
            print(f"⚠️ Image conversion failed: {e}")
            return file_path

    # HEIC
    if file_ext in ['heic', 'heif']:
        try:
            import pillow_heif
            pillow_heif.register_heif_opener()
            from PIL import Image
            img = Image.open(file_path)
            if img.mode in ('RGBA', 'LA', 'P'):
                img = img.convert('RGB')
            pdf_path = file_path.rsplit('.', 1)[0] + '_print.pdf'
            img.save(pdf_path, 'PDF', resolution=300)
            print(f"✅ HEIC converted to PDF: {pdf_path}")
            return pdf_path
        except Exception as e:
            print(f"⚠️ HEIC conversion failed: {e}")
            return file_path

    # PDF and everything else — return as-is
    return file_path


def _find_canon_printer():
    """Find Canon printer name from Windows printer list."""
    try:
        import win32print

        # Virtual printers to always skip
        SKIP = ['onenote', 'microsoft', 'pdf', 'xps', 'fax',
                'send to', 'snagit', 'notion', 'docuworks']

        printers = win32print.EnumPrinters(
            win32print.PRINTER_ENUM_LOCAL | win32print.PRINTER_ENUM_CONNECTIONS,
            None, 4
        )

        print(f"🔍 All installed printers:")
        real_printers = []
        for p in printers:
            name = p['pPrinterName']
            port = p.get('pPortName', '')
            print(f"   • {name} | Port: {port}")

            # Skip virtual printers
            if any(skip in name.lower() for skip in SKIP):
                continue
            real_printers.append({'name': name, 'port': port})

        print(f"🖨️ Real (non-virtual) printers found: {len(real_printers)}")
        for p in real_printers:
            print(f"   ✓ {p['name']} | Port: {p['port']}")

        if not real_printers:
            return None

        # Return first real printer (Canon iR2520 should be first non-virtual)
        return real_printers[0]['name']

    except ImportError:
        print("⚠️ win32print not available")
        return None
    except Exception as e:
        print(f"⚠️ Error finding printer: {e}")
        return None


def _print_via_sumatra(file_path, printer_name):
    """Print using SumatraPDF — most reliable silent printing."""
    import subprocess

    sumatra_paths = [
        r"C:\Program Files\SumatraPDF\SumatraPDF.exe",
        r"C:\Program Files (x86)\SumatraPDF\SumatraPDF.exe",
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "SumatraPDF.exe"),
    ]

    sumatra_exe = None
    for path in sumatra_paths:
        if os.path.exists(path):
            sumatra_exe = path
            break

    if not sumatra_exe:
        print("⚠️ SumatraPDF not found")
        return False

    abs_path = os.path.abspath(file_path)
    cmd = [
        sumatra_exe,
        "-print-to", printer_name,
        "-silent",
        "-exit-when-done",
        abs_path
    ]
    print(f"🖨️ SumatraPDF command: {' '.join(cmd)}")

    result = subprocess.run(cmd, timeout=60, capture_output=True, text=True)
    print(f"✅ SumatraPDF exit code: {result.returncode}")
    if result.stdout: print(f"   stdout: {result.stdout.strip()}")
    if result.stderr: print(f"   stderr: {result.stderr.strip()}")

    return result.returncode == 0


def _print_via_powershell(file_path, printer_name):
    """Print using PowerShell — fallback method."""
    import subprocess

    abs_path = os.path.abspath(file_path)
    # Use PrintTo verb with specific printer
    ps_cmd = (
        f'$printer = "{printer_name}"; '
        f'$file = "{abs_path}"; '
        f'Start-Process -FilePath $file -Verb PrintTo -ArgumentList $printer -WindowStyle Hidden -Wait'
    )
    print(f"🖨️ PowerShell print to: {printer_name}")

    result = subprocess.run(
        ["powershell", "-NoProfile", "-Command", ps_cmd],
        timeout=60,
        capture_output=True,
        text=True
    )
    print(f"✅ PowerShell exit code: {result.returncode}")
    if result.stderr: print(f"   stderr: {result.stderr.strip()}")

    return True  # PowerShell doesn't reliably return error codes for print jobs


def _print_via_win32(file_path, printer_name):
    """Print using win32print raw data write — most direct method."""
    try:
        import win32print

        abs_path = os.path.abspath(file_path)

        with open(abs_path, 'rb') as f:
            data = f.read()

        print(f"🖨️ win32print direct: {len(data)} bytes → {printer_name}")

        hprinter = win32print.OpenPrinter(printer_name)
        try:
            job = win32print.StartDocPrinter(hprinter, 1, ("Print Job", None, "RAW"))
            try:
                win32print.StartPagePrinter(hprinter)
                win32print.WritePrinter(hprinter, data)
                win32print.EndPagePrinter(hprinter)
                print(f"✅ win32print job sent: {job}")
                return True
            finally:
                win32print.EndDocPrinter(hprinter)
        finally:
            win32print.ClosePrinter(hprinter)

    except Exception as e:
        print(f"⚠️ win32print failed: {e}")
        return False


def send_to_printer(ip, port, protocol, file_path):
    """
    Send file to Canon iR2520 printer.
    Tries methods in order: SumatraPDF → PowerShell → win32print → raw socket
    """
    print_path = file_path
    try:
        # Step 1: Convert to PDF if needed
        print_path = prepare_file_for_printing(file_path)

        if not os.path.exists(print_path):
            print(f"❌ File not found: {print_path}")
            return False

        file_size = os.path.getsize(print_path)
        print(f"📄 Ready to print: {print_path} ({file_size/1024:.1f} KB)")

        import platform
        if platform.system() != 'Windows':
            # Non-Windows: raw socket only
            return _send_raw_socket(ip, port, print_path)

        # Step 2: Find the Canon printer
        printer_name = _find_canon_printer()

        if not printer_name:
            print(f"❌ No real printer found, falling back to raw socket")
            return _send_raw_socket(ip, port, print_path)

        print(f"\n{'='*50}")
        print(f"🖨️ TARGET PRINTER: {printer_name}")
        print(f"{'='*50}")

        # Step 3: Try SumatraPDF first (best method)
        print(f"\n🔵 Method 1: SumatraPDF")
        if _print_via_sumatra(print_path, printer_name):
            print(f"✅ Printed via SumatraPDF!")
            return True

        # Step 4: Try PowerShell
        print(f"\n🔵 Method 2: PowerShell")
        if _print_via_powershell(print_path, printer_name):
            print(f"✅ Printed via PowerShell!")
            return True

        # Step 5: Try win32print raw
        print(f"\n🔵 Method 3: win32print RAW")
        if _print_via_win32(print_path, printer_name):
            print(f"✅ Printed via win32print!")
            return True

        # Step 6: Raw socket last resort
        print(f"\n🔵 Method 4: Raw socket")
        return _send_raw_socket(ip, port, print_path)

    except Exception as e:
        print(f"❌ send_to_printer error: {e}")
        import traceback
        traceback.print_exc()
        return False

    finally:
        # Clean up temp converted files
        try:
            if print_path != file_path and os.path.exists(print_path):
                os.remove(print_path)
                print(f"🗑️ Cleaned up: {print_path}")
        except Exception:
            pass
def _send_raw_socket(ip, port, file_path):
    """Raw socket fallback"""
    try:
        import socket as sock
        port = int(port) if port else 9100
        print(f"🖨️ Raw socket: {file_path} → {ip}:{port}")

        with open(file_path, 'rb') as f:
            data = f.read()

        s = sock.socket(sock.AF_INET, sock.SOCK_STREAM)
        s.settimeout(30)
        s.connect((ip, port))

        chunk_size = 65536
        total_sent = 0
        for i in range(0, len(data), chunk_size):
            s.sendall(data[i:i + chunk_size])
            total_sent += len(data[i:i + chunk_size])

        s.close()
        print(f"✅ Raw socket sent {total_sent} bytes to {ip}:{port}")
        return True
    except Exception as e:
        print(f"❌ Raw socket failed: {e}")
        return False
def send_batched_confirmation(phone, session_id):
    """
    Send a single confirmation for all files uploaded in the batch
    This runs after the timer expires (no new files for 2 seconds)
    """
    with pending_confirmations[phone]['lock']:
        files = pending_confirmations[phone]['files']
        
        if not files:
            return
        
        print(f"\n{'='*50}")
        print(f"📤 Sending batched confirmation for {len(files)} file(s)")
        print(f"{'='*50}\n")
        
        web_url = f"{NGROK_URL}/order/{session_id}"
        
        if len(files) == 1:
            # Single file - simple message
            f = files[0]
            icon = '🖼️' if f['type'] == 'image' else '📄'
            confirmation = (
                f"✅ *File Received!*\n\n"
                f"{icon} {f['name']}\n"
                f"📃 Pages: {f['pages']}\n\n"
                f"➕ Send more files or configure:\n{web_url}"
            )
        else:
            # Multiple files - show list
            file_list = "\n".join([
                f"{i+1}. {'🖼️' if f['type'] == 'image' else '📄'} {f['name']} ({f['pages']} pg)"
                for i, f in enumerate(files)
            ])
            
            total_pages = sum(f['pages'] for f in files)
            
            confirmation = (
                f"✅ *{len(files)} Files Received!*\n\n"
                f"{file_list}\n\n"
                f"📃 Total Pages: {total_pages}\n\n"
                f"➕ Send more or configure:\n{web_url}"
            )
        
        whatsapp_session = None
        with sessions_lock:
            if phone in sessions:
                whatsapp_session = sessions[phone].get("whatsapp_session_id")

        send_whatsapp_text(phone, confirmation, session_id=whatsapp_session)
                    
        # Clear the batch
        pending_confirmations[phone]['files'] = []
        pending_confirmations[phone]['timer'] = None
        
        print(f"✅ Batch confirmation sent!\n")


def schedule_confirmation(phone, session_id, filename, file_type, pages, delay=2.0):
    """
    Schedule a batched confirmation with debouncing
    
    How it works:
    1. File received → Add to batch, start 2-second timer
    2. Another file → Add to batch, CANCEL old timer, start NEW 2-second timer
    3. Another file → Add to batch, CANCEL old timer, start NEW 2-second timer
    4. No files for 2 seconds → Timer expires → Send ONE message with all files
    
    Args:
        phone: User's phone number
        session_id: Session ID
        filename: Name of the file
        file_type: 'image' or 'document'
        pages: Number of pages
        delay: Seconds to wait before sending (default 2.0)
    """
    with pending_confirmations[phone]['lock']:
        # Add file to batch
        pending_confirmations[phone]['files'].append({
            'name': filename,
            'type': file_type,
            'pages': pages
        })
        
        batch_size = len(pending_confirmations[phone]['files'])
        
        # Cancel existing timer if there is one
        if pending_confirmations[phone]['timer']:
            pending_confirmations[phone]['timer'].cancel()
            print(f"⏰ Cancelled previous timer (now {batch_size} files in batch)")
        
        # Schedule new timer
        timer = threading.Timer(
            delay, 
            send_batched_confirmation, 
            args=[phone, session_id]
        )
        timer.daemon = True  # Don't block app shutdown
        timer.start()
        
        pending_confirmations[phone]['timer'] = timer
        
        print(f"⏰ Scheduled confirmation in {delay}s (batch: {batch_size} file(s))")

def is_valid_one_to_one_message(remote_jid):
    """
    Check if the message is a valid 1-to-1 message.
    Returns True only for individual chats.
    """
    if not remote_jid:
        return False
    
    jid_lower = remote_jid.lower()
    
    # ✅ REJECT these explicitly (groups, channels, communities, status)
    if '@g.us' in jid_lower:
        return False  # Group
    if '@newsletter' in jid_lower:
        return False  # Channel/Newsletter
    if '@broadcast' in jid_lower:
        return False  # Status update
    if '@lid' in jid_lower:     
        number_part = jid_lower.split('@')[0]
        if len(number_part) > 15:
            return False  # Community/group lid
        # Individual @lid — accept it (same logic as bot.js)
    
    # ✅ ACCEPT everything else (individual chats)
    # This includes @s.whatsapp.net, @c.us, and any other individual format
    return True

def send_whatsapp_text(to_phone, text, session_id=None):
    """Send WhatsApp message via Node.js bot"""
    
    if not session_id:
        print("❌ ERROR: session_id is required for sending messages")
        return None
    
    url = f"{NODEJS_BOT_URL}/api/send"
    
    payload = {
        "session_id": session_id,
        "phone": to_phone,
        "message": text
    }
    
    print(f"\n{'='*50}")
    print(f"📤 SENDING WHATSAPP MESSAGE")
    print(f"{'='*50}")
    print(f"🔄 Session: {session_id}")
    print(f"🔄 To: {to_phone}")
    print(f"📋 Message: {text[:100]}...")
    print(f"{'='*50}\n")
    
    try:
        # ✅ ADDED: Check session status first
        status_response = requests.get(f"{NODEJS_BOT_URL}/api/status/{session_id}", timeout=5)
        if status_response.ok:
            status_data = status_response.json()
            if not status_data.get('connected'):
                print(f"⚠️ Session {session_id} not connected (status: {status_data.get('status')})")
                print(f"⚠️ Message will be queued or skipped")
                # You can either return None or queue the message
                return None
        
        r = requests.post(url, json=payload, timeout=30)
        print(f"📊 Response Status: {r.status_code}")
        print(f"📊 Response Body: {r.text}")
        r.raise_for_status()
        return r.json()
    except requests.exceptions.Timeout:
        print(f"⚠️ Request timeout (message may still be sending)")
        return None
    except Exception as e:
        print(f"❌ Error: {e}")
        if 'r' in locals():
            print(f"❌ Full Response: {r.text}")
        import traceback
        traceback.print_exc()
        return None

def download_or_read_media(url):
    """
    Handle HTTP URLs, file:// URLs, and local paths - OPTIMIZED
    Returns: bytes
    """
    try:
        # Case 1: HTTP/HTTPS URLs (WhatsApp media served via Node.js)
        if url.startswith('http://') or url.startswith('https://'):
            print(f"📥 Downloading from HTTP: {url}")
            response = requests.get(url, timeout=10, stream=True)  # ✅ Add timeout + stream
            response.raise_for_status()
            
            # ✅ Stream download for large files
            chunks = []
            for chunk in response.iter_content(chunk_size=8192):
                if chunk:
                    chunks.append(chunk)
            
            file_data = b''.join(chunks)
            print(f"✅ Downloaded {len(file_data)} bytes")
            return file_data
        
        # Case 2: file:// URLs (legacy WhatsApp)
        elif url.startswith('file://'):
            from urllib.parse import urlparse, unquote
            parsed = urlparse(url)
            file_path = unquote(parsed.path)
            
            # Fix Windows paths
            if os.name == 'nt' and file_path.startswith('/') and ':' in file_path:
                file_path = file_path[1:]
            
            file_path = os.path.normpath(file_path)
            print(f"📂 Reading from file:// URL: {file_path}")
            
            if not os.path.exists(file_path):
                raise FileNotFoundError(f"File not found: {file_path}")
            
            # Retry logic for file locks
            max_retries = 3
            for attempt in range(max_retries):
                try:
                    with open(file_path, 'rb') as f:
                        data = f.read()
                    print(f"✅ Read {len(data)} bytes")
                    return data
                except PermissionError:
                    if attempt < max_retries - 1:
                        print(f"⚠️ Retry {attempt + 1}/{max_retries}")
                        import time
                        time.sleep(0.5)
                    else:
                        raise
        
        # Case 3: Already a local path (website uploads)
        else:
            # Treat as local file path
            file_path = url
            print(f"📂 Reading local file: {file_path}")
            
            if not os.path.exists(file_path):
                raise FileNotFoundError(f"File not found: {file_path}")
            
            with open(file_path, 'rb') as f:
                data = f.read()
            print(f"✅ Read {len(data)} bytes")
            return data
            
    except Exception as e:
        print(f"❌ Media access error ({type(e).__name__}): {e}")
        import traceback
        traceback.print_exc()
        raise

def download_media_fast(media_url, filename):
    """
    Download/read media and save to UPLOAD_DIR - OPTIMIZED
    Handles:
    - HTTP URLs (WhatsApp via Node.js)
    - file:// URLs (legacy)
    - Local file paths (website uploads - just return as-is)
    
    Returns: (local_path, original_url)
    """
    try:
        print(f"📥 Processing: {filename}")
        
        # ✅ Check if already in UPLOAD_DIR (instant)
        if str(UPLOAD_DIR) in media_url:
            print(f"✅ Already local: {filename}")
            return media_url, media_url
        
        # ✅ Get file bytes
        file_data = download_or_read_media(media_url)
        
        # ✅ Save to upload directory
        path = UPLOAD_DIR / filename
        
        # ✅ FASTER: Write in chunks for large files
        with open(path, "wb") as f:
            if len(file_data) > 1024 * 1024:  # If > 1MB, write in chunks
                chunk_size = 64 * 1024  # 64KB chunks
                for i in range(0, len(file_data), chunk_size):
                    f.write(file_data[i:i+chunk_size])
            else:
                f.write(file_data)
        
        print(f"✅ Saved: {filename} ({len(file_data)} bytes)")
        return str(path), media_url
        
    except Exception as e:
        print(f"❌ download_media_fast error: {e}")
        import traceback
        traceback.print_exc()
        raise
def get_file_extension(filename):
    return filename.lower().rsplit('.', 1)[-1] if '.' in filename else ''

def count_pages_smart(file_path, file_ext):
    """Count pages based on file type - OPTIMIZED VERSION"""
    try:
        # PDF files - Use fast metadata reading
        if file_ext == 'pdf':
            try:
                # ✅ FASTER: Use pikepdf instead of PyPDF2 (10x faster)
                import pikepdf
                with pikepdf.open(file_path) as pdf:
                    return len(pdf.pages)
            except ImportError:
                # Fallback to PyPDF2 if pikepdf not installed
                from PyPDF2 import PdfReader
                with open(file_path, 'rb') as f:
                    reader = PdfReader(f)
                    return len(reader.pages)
        
        # Image files - INSTANT response (no need to open)
        elif file_ext in SUPPORTED_FORMATS['image']:
            # HEIC/HEIF - always 1 page
            if file_ext in ['heic', 'heif']:
                return 1
            
            # TIFF - can have multiple pages (but rare)
            elif file_ext in ['tiff', 'tif']:
                try:
                    from PIL import Image
                    with Image.open(file_path) as img:
                        return getattr(img, 'n_frames', 1)
                except:
                    return 1
            
            # ✅ ALL OTHER IMAGES: Just return 1 (no need to open file)
            else:
                return 1
        
        # Document files - Estimate based on file size (INSTANT)
        elif file_ext in SUPPORTED_FORMATS['document']:
            file_size = os.path.getsize(file_path)
            
            # ✅ FASTER: Just estimate, don't parse
            if file_ext == 'txt':
                return max(1, file_size // 3000)
            elif file_ext in ['doc', 'docx']:
                return max(1, file_size // 50000)
            else:
                return max(1, file_size // 40000)
        
        # Unknown formats
        else:
            return 1
            
    except Exception as e:
        print(f"⚠️ Page count error (using fallback): {e}")
        return 1
def is_supported_format(filename):
    ext = get_file_extension(filename)
    all_formats = []
    for formats in SUPPORTED_FORMATS.values():
        all_formats.extend(formats)
    return ext in all_formats

@app.route("/")
def home():
    return "WhatsApp Print Shop Bot is running!"

WEBHOOK_SECRET = os.getenv("WEBHOOK_SECRET")

@app.route("/webhook", methods=["GET", "POST"])
def webhook():
    if request.method == "POST":
        # Auth: accept requests from localhost (same machine) or valid signature
        remote_addr = request.remote_addr
        sig = request.headers.get("X-Webhook-Signature", "")

        if remote_addr in ('127.0.0.1', '::1', 'localhost'):
            # Same machine — trust it, no signature needed
            pass
        elif WEBHOOK_SECRET and sig:
            import hmac as hmac_lib, hashlib
            mac = hmac_lib.new(WEBHOOK_SECRET.encode(), request.get_data(), hashlib.sha256)
            expected = mac.hexdigest()
            if not hmac_lib.compare_digest(sig, expected):
                print(f"❌ Webhook signature mismatch from {remote_addr}")
                return jsonify({"error": "Unauthorized"}), 401
        else:
            print(f"❌ Webhook request from unknown origin {remote_addr} with no signature")
            return jsonify({"error": "Unauthorized"}), 401
    
    # GET: Webhook verification
    if request.method == "GET":
        verify_token = os.getenv("WEBHOOK_VERIFY_TOKEN", "verifytoken123")
        mode = request.args.get("hub.mode")
        token = request.args.get("hub.verify_token")
        challenge = request.args.get("hub.challenge")

        if mode == "subscribe" and token == verify_token:
            return challenge, 200
        return "Verification failed", 403
    
    # POST: Handle incoming messages
    try:
        data = request.get_json(force=True)
        # Replace the full dump with a safe summary:
        print("\n" + "="*60)
        print("📨 WEBHOOK RECEIVED")
        print(f"   Event: {data.get('event', 'unknown')}")
        print(f"   Session: {data.get('sessionId', 'unknown')}")
        print("="*60 + "\n")

        # Only do the full dump in debug mode:
        if os.getenv('FLASK_DEBUG', 'false').lower() == 'true':
            print(json.dumps(data, indent=2))
                
        # ============ EXTRACT DATA ============
        event = data.get('event', '')
        webhook_data = data.get('data', {})
        messages_data = webhook_data.get('messages', {})
        
        # Get sender info
        key = messages_data.get('key', {})
        from_phone = key.get('remoteJid', '')
        from_me = key.get('fromMe', False)
        
        if not is_valid_one_to_one_message(from_phone):
            print(f"⏭️ IGNORING non-1-to-1 message from: {from_phone}\n")
            return jsonify({"status": "ignored", "reason": "not_individual_chat"}), 200
        # ============ FILTERING ============
        
        # Skip messages from bot itself
        print(f"⚠️ Processing message from: {from_phone}")
        if from_me:
            print("⏭️ IGNORING message from bot itself\n")
            return jsonify({"status": "ignored", "reason": "from_me"}), 200
        
        # Check for null/empty message object
        message_obj = messages_data.get('message')
        if not message_obj or message_obj is None:
            print("⏭️ IGNORING message with null/empty message object\n")
            return jsonify({"status": "ignored", "reason": "null message"}), 200
        
        # Get message body
        message_body = (
            messages_data.get('messageBody', '') or
            message_obj.get('conversation', '') or
            (message_obj.get('extendedTextMessage', {}) or {}).get('text', '') or
            (message_obj.get('imageMessage', {}) or {}).get('caption', '') or
            (message_obj.get('documentMessage', {}) or {}).get('caption', '') or
            ''
        ).strip()
        
        # Determine message type
        if 'imageMessage' in message_obj:
            message_type = 'image'
        elif 'documentMessage' in message_obj:
            message_type = 'document'
        elif message_body:
            message_type = 'text'
        else:
            message_type = 'unknown'
        
        print(f"📱 From: {from_phone}")
        print(f"📋 Type: {message_type}")
        print(f"💬 Message: {message_body[:100] if message_body else '[no text]'}")
        
        # Skip if no meaningful content
        if message_type == 'unknown' or (message_type == 'text' and not message_body):
            print("⏭️ IGNORING message with no content\n")
            return jsonify({"status": "ignored", "reason": "no content"}), 200
        
        # Get and validate message timestamp
        message_timestamp = messages_data.get('messageTimestamp') or messages_data.get('timestamp') or 0
        
        # Handle both dict and direct values
        if isinstance(message_timestamp, dict):
            message_timestamp = message_timestamp.get('low', 0)
        elif isinstance(message_timestamp, str):
            message_timestamp = int(message_timestamp)
        
        print(f"⏰ Message timestamp: {message_timestamp}")
        print(f"⏰ Bot start time: {BOT_START_TIME}")

        # IGNORE OLD MESSAGES (sent before bot started)
        if message_timestamp < BOT_START_TIME:
            print(f"⏭️ IGNORING old message (before bot started)")
            print(f"   Message time: {datetime.fromtimestamp(message_timestamp)}")
            print(f"   Bot started: {datetime.fromtimestamp(BOT_START_TIME)}\n")
            return jsonify({"status": "ignored", "reason": "old message"}), 200

        print(f"✅ New message - processing...\n")
        
        # ============ SESSION MANAGEMENT ============

        # ✅ Get WhatsApp session ID from webhook
        webhook_session_id = data.get('sessionId')  # This comes from Node.js

        if not webhook_session_id:
            print("⚠️ No session ID in webhook, skipping message")
            return jsonify({"status": "ignored", "reason": "no session"}), 200

        print(f"\n{'='*60}")
        print(f"📱 INCOMING MESSAGE TO SHOP WHATSAPP")
        print(f"{'='*60}")
        print(f"Session ID (Shop's WhatsApp): {webhook_session_id}")
        print(f"From (Customer): {from_phone}")
        print(f"{'='*60}\n")

        # ✅ Find which shop owns this WhatsApp session
        # This is the ONLY lookup needed - by session_id (e.g., SHOP_D2B55310)
        shop_info = get_shop_by_whatsapp_session(webhook_session_id)

        if not shop_info or not shop_info.get('success'):
            print(f"❌ Unknown session {webhook_session_id}")
            print(f"⚠️ This WhatsApp account is not registered to any shop")
            print(f"⚠️ Shop needs to scan QR code in dashboard first")
            return jsonify({"status": "ignored", "reason": "unknown shop"}), 200

        shop_data = shop_info.get('shop', {})
        print(f"✅ Found shop: {shop_data.get('shop_name')}")
        print(f"   Shop ID: {shop_data.get('shop_id')}")
        print(f"   Database ID: {shop_data.get('id')}")
        print(f"   Customer messaging: {from_phone}\n")

        
        with sessions_lock:
            if from_phone not in sessions:
                session_id = uuid.uuid4().hex[:12].upper()
                sessions[from_phone] = {
                    "session_id": session_id,
                    "whatsapp_session_id": webhook_session_id,
                    "shop_id": shop_data.get('shop_id'),
                    "shop_database_id": shop_data.get('id'),
                    "order_placed": False,
                    "order_data": {
                        "order_id": f"ORD_{uuid.uuid4().hex[:8].upper()}",
                        "session_id": session_id,
                        "user_id": from_phone,
                        "timestamp": datetime.utcnow().isoformat(),
                        "files": [],
                        "total_price": None,
                        "total_pages": None,
                        "total_sheets": None,
                        "payment_status": "pending",
                        "order_status": "pending"
                    }
                }
                print(f"✅ Created new session for customer: {from_phone}")
                print(f"   Session ID: {session_id}")
                print(f"   Linked to shop: {shop_data.get('shop_name')}\n")

            job = sessions[from_phone]
            session_id = job["session_id"]
        
        # ============ HANDLE TEXT MESSAGES ============
        if message_type == "text" and message_body:
            whatsapp_session = job.get("whatsapp_session_id")
            message_lower = message_body.lower()
            
            if message_lower in ['hi', 'hello', 'start', 'hey']:
                # ✅ FIXED: Reset session but PRESERVE WhatsApp session and shop info
                old_whatsapp_session = job.get("whatsapp_session_id")
                old_shop_id = job.get("shop_id")
                old_shop_db_id = job.get("shop_database_id")
                
                # Create new session
                session_id = uuid.uuid4().hex[:12].upper()
                
                with sessions_lock:
                    sessions[from_phone] = {
                        "session_id": session_id,
                        "whatsapp_session_id": old_whatsapp_session,
                        "shop_id": old_shop_id,
                        "shop_database_id": old_shop_db_id,
                        "order_placed": False,
                        "order_data": {
                            "order_id": f"ORD_{uuid.uuid4().hex[:8].upper()}",
                            "session_id": session_id,
                            "user_id": from_phone,
                            "timestamp": datetime.utcnow().isoformat(),
                            "files": [],
                            "total_price": None,
                            "total_pages": None,
                            "total_sheets": None,
                            "payment_status": "pending",
                            "order_status": "pending"
                        }
                    }
                
                print(f"🔄 Session reset with preserved WhatsApp session: {old_whatsapp_session}")
                print(f"   New session ID: {session_id}")
                
                # Combine greeting and link in ONE message
                web_url = f"{NGROK_URL}/order/{session_id}"
                greeting = (
                    "👋 *Welcome to Print Shop!*\n\n"
                    "💰 *Pricing:*\n"
                    "• B&W: ₹1.1/sheet\n"
                    "• Color: ₹6/sheet\n\n"
                    "📤 *How to Order:*\n"
                    "1. Send PDF/Image files\n"
                    "2. Configure print options\n"
                    "3. Complete payment\n\n"
                    "📎 Send your first file now!\n\n"
                    f"🔗 {web_url}"
                )
                
                # ✅ Use preserved session
                if old_whatsapp_session:
                    send_whatsapp_text(from_phone, greeting, session_id=old_whatsapp_session)
                else:
                    print("⚠️ No WhatsApp session to send message to")
                
            elif message_lower in ['help', 'menu', '?']:
                help_text = (
                    "🆘 *Print Shop Help*\n\n"
                    "📤 *Send:* PDF, Images, Documents\n"
                    "💰 *Pricing:* B&W ₹1.1, Color ₹6/sheet\n"
                    "🔗 *Configure:* Use web link\n"
                    "💳 *Payment:* PhonePe/UPI\n\n"
                    "📝 *Commands:*\n"
                    "• hi - New order\n"
                    "• status - Check order\n"
                    "• help - This menu"
                )
                if whatsapp_session:
                    send_whatsapp_text(from_phone, help_text, session_id=whatsapp_session)
                else:
                    print("⚠️ No WhatsApp session to send message to")
                
            elif message_lower in ['status', 'order', 'check']:
                if job["order_data"]["files"]:
                    files_count = len(job["order_data"]["files"])
                    web_url = f"{NGROK_URL}/order/{session_id}"
                    status_text = (
                        f"📊 *Order Status*\n\n"
                        f"📁 Files Uploaded: {files_count}\n\n"
                        f"🔗 Configure here:\n{web_url}"
                    )
                    if whatsapp_session:
                        send_whatsapp_text(from_phone, status_text, session_id=whatsapp_session)
                    else:
                        print("⚠️ No WhatsApp session to send message to")
                else:
                    if whatsapp_session:
                        send_whatsapp_text(
                            from_phone,
                            "📭 No files yet.\n\n"
                            "📎 Send PDF/image to start!",
                            session_id=whatsapp_session
                        )
                    else:
                        print("⚠️ No WhatsApp session to send message to")
            
            else:
                # Any other text
                web_url = f"{NGROK_URL}/order/{session_id}"
                if whatsapp_session:
                    send_whatsapp_text(
                        from_phone,
                        "💬 Message received!\n\n"
                        f"📎 Configure order:\n{web_url}",
                        session_id=whatsapp_session
                    )
                else:
                    print("⚠️ No WhatsApp session to send message to")
        
        # ============ HANDLE DOCUMENT UPLOADS ============
        elif message_type == "document":
            whatsapp_session = job.get("whatsapp_session_id")
            doc_msg = message_obj.get('documentMessage', {})
            
            filename = doc_msg.get('fileName', f"doc_{uuid.uuid4().hex[:8]}.pdf")
            mime_type = doc_msg.get('mimetype', 'application/pdf')
            media_url = doc_msg.get('url', '')
            
            print(f"📄 Document: {filename}")
            
            if not is_supported_format(filename):
                if whatsapp_session:
                    send_whatsapp_text(
                        from_phone,
                        f"❌ *Unsupported Format*\n\n"
                        f"File: {filename}\n\n"
                        f"✅ Send: PDF, JPG, PNG, DOCX",
                        session_id=whatsapp_session
                    )
                return jsonify({"status": "received"}), 200
            
            try:
                # ✅ STEP 1: Download file (fast)
                unique_filename = f"{uuid.uuid4().hex[:8]}_{filename}"
                local_path, file_url = download_media_fast(media_url, unique_filename)
                
                file_ext = get_file_extension(filename)
                
                # ✅ STEP 2: Add to order with placeholder page count (INSTANT)
                file_id = f"FILE_{len(job['order_data']['files']) + 1}"
                file_obj = {
                    "file_id": file_id,
                    "file_url": file_url,
                    "filename": filename,
                    "file_type": file_ext,
                    "local_path": local_path,
                    "print_options": {
                        "color": False,
                        "sides": "double",
                        "copies": 1
                    },
                    "page_count": None,  # ✅ Will be updated in background
                    "sheets_required": None,
                    "total_sheets": None,
                    "price": None,
                    "processing_status": "processing"  # ✅ Mark as processing
                }
                
                job["order_data"]["files"].append(file_obj)
                print(f"✅ File queued: {filename}")
                
                # ✅ STEP 3: Send INSTANT confirmation
                icon = '📄'
                if whatsapp_session:
                    send_whatsapp_text(
                        from_phone,
                        f"✅ *File Received!*\n\n"
                        f"{icon} {filename}\n"
                        f"⏳ Processing...\n\n"
                        f"Send more files or check status.",
                        session_id=whatsapp_session
                    )
                
                # ✅ STEP 4: Count pages in BACKGROUND (doesn't block)
                def process_pages_background():
                    try:
                        print(f"🔄 Background processing: {filename}")
                        pages = count_pages_smart(local_path, file_ext)
                        
                        if pages is None or pages <= 0:
                            pages = 1
                        
                        # Update the file object
                        file_obj["page_count"] = pages
                        file_obj["processing_status"] = "pending"
                        
                        print(f"✅ Background complete: {filename} ({pages} pages)")
                        
                        # ✅ Send update notification
                        if whatsapp_session and pages > 0:
                            web_url = f"{NGROK_URL}/order/{session_id}"
                            send_whatsapp_text(
                                from_phone,
                                f"✅ {filename}\n"
                                f"📃 {pages} page{'s' if pages != 1 else ''} detected\n\n"
                                f"🔗 Configure: {web_url}",
                                session_id=whatsapp_session
                            )
                        
                    except Exception as e:
                        print(f"❌ Background processing error: {e}")
                        file_obj["processing_status"] = "error"
                
                # Start background thread
                import threading
                thread = threading.Thread(target=process_pages_background, daemon=True)
                thread.start()
                
            except Exception as e:
                print(f"❌ Error: {e}")
                import traceback
                traceback.print_exc()
                if whatsapp_session:
                    send_whatsapp_text(
                        from_phone,
                        f"❌ *Processing Failed*\n\n"
                        f"{filename}\n\n"
                        f"Please try again.",
                        session_id=whatsapp_session
                    )

        # ============ HANDLE IMAGE UPLOADS ============
        elif message_type == "image":
            whatsapp_session = job.get("whatsapp_session_id")
            
            print("\n" + "="*50)
            print("🖼️ IMAGE MESSAGE PROCESSING")
            print("="*50)
            
            img_msg = message_obj.get('imageMessage', {})
            
            mime_type = img_msg.get('mimetype', 'image/jpeg')
            ext = mime_type.split('/')[-1].replace('jpeg', 'jpg')
            filename = f"img_{uuid.uuid4().hex[:8]}.{ext}"
            media_url = img_msg.get('url', '')
            
            print(f"📋 Filename: {filename}")
            print(f"📋 Media URL: {media_url}")
            
            if not media_url:
                print("❌ No media URL found!")
                if whatsapp_session:
                    send_whatsapp_text(from_phone, "❌ Failed to get image URL", session_id=whatsapp_session)
                return jsonify({"status": "received"}), 200
            
            if not is_supported_format(filename):
                print(f"❌ Unsupported format: {filename}")
                if whatsapp_session:
                    send_whatsapp_text(from_phone, f"❌ Unsupported image format", session_id=whatsapp_session)
                return jsonify({"status": "received"}), 200
            
            try:
                # ✅ STEP 1: Download file (fast)
                unique_filename = f"{uuid.uuid4().hex[:8]}_{filename}"
                local_path, file_url = download_media_fast(media_url, unique_filename)
                print(f"✅ Downloaded to {local_path}")
                
                file_ext = get_file_extension(filename)
                
                # ✅ STEP 2: Add to order (images are always 1 page - INSTANT)
                file_id = f"FILE_{len(job['order_data']['files']) + 1}"
                file_obj = {
                    "file_id": file_id,
                    "file_url": file_url,
                    "filename": filename,
                    "file_type": file_ext,
                    "local_path": local_path,
                    "print_options": {
                        "color": False,
                        "sides": "double",
                        "copies": 1
                    },
                    "page_count": 1,  # ✅ Images are always 1 page (instant)
                    "processing_status": "pending"
                }
                
                job["order_data"]["files"].append(file_obj)
                print(f"✅ Added to order (1 page)")
                
                # ✅ STEP 3: Send INSTANT confirmation
                if whatsapp_session:
                    send_whatsapp_text(
                        from_phone,
                        f"✅ *Image Received!*\n\n"
                        f"🖼️ {filename}\n"
                        f"📃 1 page\n\n"
                        f"Send more files or check status.",
                        session_id=whatsapp_session
                    )
                
                print("="*50 + "\n")
                
            except Exception as e:
                print(f"❌ Error: {e}")
                import traceback
                traceback.print_exc()
                if whatsapp_session:
                    send_whatsapp_text(from_phone, f"❌ Failed to process image", session_id=whatsapp_session)
        
        return jsonify({"status": "received"}), 200
        
    except Exception as e:
        print(f"❌ Webhook error: {e}")
        import traceback
        traceback.print_exc()
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route("/order/<session_id>")
def order_page(session_id):
    """Web interface for configuring print order"""
    
    # Check if session exists, if not create it
    session_exists = False
    for phone, job in sessions.items():
        if job.get("session_id") == session_id:
            session_exists = True
            break
    
    # If session doesn't exist, create a dummy one for testing
    if not session_exists:
        print(f"⚠️ Session {session_id} not found, creating new session...")
        
        # Use session_id as phone number for web-only orders
        phone = f"web_{session_id}"
        
        # ✅ Try to get shop info for this session
        shop_info = get_shop_by_whatsapp_session(session_id)
        whatsapp_session_id = None
        shop_id = None
        shop_db_id = None
        
        if shop_info and shop_info.get('success'):
            shop_data = shop_info.get('shop', {})
            whatsapp_session_id = shop_data.get('whatsapp_session_id')
            shop_id = shop_data.get('shop_id')
            shop_db_id = shop_data.get('id')
            print(f"✅ Found shop info: {shop_data.get('shop_name')}")
        
        with sessions_lock:
            sessions[phone] = {
                "session_id": session_id,
                "whatsapp_session_id": whatsapp_session_id,  # ✅ ADD
                "shop_id": shop_id,                          # ✅ ADD
                "shop_database_id": shop_db_id,              # ✅ ADD
                "order_placed": False,
                "order_data": {
                    "order_id": f"ORD_{uuid.uuid4().hex[:8].upper()}",
                    "session_id": session_id,
                    "user_id": phone,
                    "timestamp": datetime.utcnow().isoformat(),
                    "files": [],
                    "total_price": None,
                    "total_pages": None,
                    "total_sheets": None,
                    "payment_status": "pending",
                    "order_status": "pending"
                }
            }
        
        print(f"✅ Created session for {phone}")
    
    return render_template('order-config.html', session_id=session_id)

@app.route("/api/order/<session_id>")
def get_order_api(session_id):
    """Get order data by session ID"""
    for phone, job in sessions.items():
        if job.get("session_id") == session_id:
            return jsonify(job["order_data"])
    return jsonify({"files": []})

@app.route("/api/order-status/<order_id>")
def get_order_status(order_id):
    """Get order status by order_id (for payment status checking)"""
    for phone, job in sessions.items():
        if job["order_data"]["order_id"] == order_id:
            return jsonify({
                "success": True,
                "order_data": {
                    "order_id": job["order_data"]["order_id"],
                    "payment_status": job["order_data"].get("payment_status", "pending"),
                    "order_status": job["order_data"].get("order_status", "pending")
                }
            })
    return jsonify({"success": False, "error": "Order not found"}), 404
@app.route("/api/upload", methods=["POST"])
def upload_files():
    """Handle file uploads from web interface"""
    session_id = None
    uploaded_files = []
    
    try:
        print("📤 Upload request started")
        
        # ✅ SAFER: Get session_id from args if not in form
        session_id = request.args.get('session_id') or request.form.get('session_id')
        
        if not session_id:
            return jsonify({"success": False, "error": "Session ID required"}), 400
        
        print(f"✅ Session ID: {session_id}")
        
        # Get files
        uploaded_files = request.files.getlist('files')
        
        if not uploaded_files:
            return jsonify({"success": False, "error": "No files uploaded"}), 400
        
        print(f"✅ Received {len(uploaded_files)} file(s)")
        
        # Find session
        job = None
        phone = None
        for p, sess in sessions.items():
            if sess.get("session_id") == session_id:
                job = sess
                phone = p
                break
        # If session not found, create it (for web-only access)
        if not job:
            print(f"⚠️ Session {session_id} not found in upload, creating new session...")
            phone = f"web_{session_id}"
            
            # ✅ Try to get shop info for this session
            shop_info = get_shop_by_whatsapp_session(session_id)
            whatsapp_session_id = None
            shop_id = None
            shop_db_id = None
            
            if shop_info and shop_info.get('success'):
                shop_data = shop_info.get('shop', {})
                whatsapp_session_id = shop_data.get('whatsapp_session_id')
                shop_id = shop_data.get('shop_id')
                shop_db_id = shop_data.get('id')
                print(f"✅ Found shop info: {shop_data.get('shop_name')}")
            with sessions_lock:
                sessions[phone] = {
                    "session_id": session_id,
                    "whatsapp_session_id": whatsapp_session_id,  # ✅ ADD
                    "shop_id": shop_id,                          # ✅ ADD
                    "shop_database_id": shop_db_id,              # ✅ ADD
                    "order_placed": False,
                    "order_data": {
                        "order_id": f"ORD_{uuid.uuid4().hex[:8].upper()}",
                        "session_id": session_id,
                        "user_id": phone,
                        "timestamp": datetime.utcnow().isoformat(),
                        "files": [],
                        "total_price": None,
                        "total_pages": None,
                        "total_sheets": None,
                        "payment_status": "pending",
                        "order_status": "pending"
                    }
                }
                job = sessions[phone]
            print(f"✅ Created session for {phone}")
        
        print(f"✅ Session found for phone: {job['order_data']['user_id']}")
        
        uploaded_count = 0
        errors = []
        
        for file in uploaded_files:
            if not file or not file.filename:
                print("⚠️ Empty file or no filename")
                continue
                
            filename = file.filename
            print(f"Processing file: {filename}")
            
            # Check if supported format
            if not is_supported_format(filename):
                error_msg = f"Unsupported format: {filename}"
                print(f"⚠️ {error_msg}")
                errors.append(error_msg)
                continue
            
            try:
                # Generate unique filename to avoid conflicts
                unique_filename = f"{uuid.uuid4().hex[:8]}_{secure_filename(filename)}"
                # Also enforce final path is within UPLOAD_DIR:
                file_path = (UPLOAD_DIR / unique_filename).resolve()
                if not str(file_path).startswith(str(UPLOAD_DIR.resolve())):
                    return jsonify({"success": False, "error": "Invalid filename"}), 400
                # Save file
                file.save(str(file_path))
                print(f"✅ Saved to: {file_path}")
                
                # Verify file was saved
                if not file_path.exists():
                    raise Exception("File not saved to disk")
                
                file_size = os.path.getsize(file_path)
                print(f"File size: {file_size} bytes")
                
                # Count pages
                file_ext = get_file_extension(filename)
                pages = count_pages_smart(str(file_path), file_ext)
                print(f"Page count: {pages}")
                
                # Add to order
                file_id = f"FILE_{len(job['order_data']['files']) + 1}"
                file_obj = {
                    "file_id": file_id,
                    "filename": filename,
                    "file_type": file_ext,
                    "local_path": str(file_path),
                    "print_options": {
                        "color": False,
                        "sides": "double",
                        "copies": 1
                    },
                    "page_count": pages,
                    "processing_status": "pending"
                }
                
                job["order_data"]["files"].append(file_obj)
                uploaded_count += 1
                print(f"✅ Added to order: {filename} ({pages} pages)")
                
            except Exception as e:
                error_msg = f"Error processing {filename}: {str(e)}"
                print(f"❌ {error_msg}")
                errors.append(error_msg)
                import traceback
                traceback.print_exc()
                continue
        
        if uploaded_count == 0:
            error_detail = " | ".join(errors) if errors else "Unknown error"
            return jsonify({
                "success": False, 
                "error": f"No files were successfully uploaded. {error_detail}"
            })
        
        print(f"✅ Successfully uploaded {uploaded_count} file(s)")
        return jsonify({
            "success": True, 
            "files": job["order_data"]["files"],
            "uploaded_count": uploaded_count,
            "errors": errors if errors else None
        })
        
    except Exception as e:
        print(f"❌ Upload error: {e}")
        import traceback
        traceback.print_exc()
        return jsonify({"success": False, "error": str(e)})

@app.route("/api/update", methods=["POST"])
def update_order():
    """Update order data"""
    try:
        data = request.json
        session_id = data.get('session_id')
        files = data.get('files')
        
        if not session_id:
            return jsonify({"success": False, "error": "Session ID required"})
        
        for phone, job in sessions.items():
            if job.get("session_id") == session_id:
                job["order_data"]["files"] = files
                return jsonify({"success": True})
        
        return jsonify({"success": False, "error": "Session not found"})
        
    except Exception as e:
        print(f"❌ Update error: {e}")
        return jsonify({"success": False, "error": str(e)})

@app.route("/payment-success")
def payment_success():
    """
    ✅ FIXED: Payment success page with proper order status checking
    """
    order_id = request.args.get('order_id')
    
    # ✅ NEW: Find the order and check its actual payment status
    order_found = False
    payment_confirmed = False
    
    if order_id:
        for phone, job in sessions.items():
            if job["order_data"]["order_id"] == order_id:
                order_found = True
                current_payment_status = job["order_data"].get("payment_status", "pending")
                
                print(f"\n🔍 Payment success page for order {order_id}")
                print(f"   Current payment status: {current_payment_status}")
                
                # ✅ CRITICAL: Only show success if payment is actually "paid"
                if current_payment_status == "paid":
                    payment_confirmed = True
                    print(f"   ✅ Payment confirmed!")
                else:
                    print(f"   ⏳ Payment still {current_payment_status}")
                
                break
    
    # ✅ FIXED: Only verify if not already verifying and payment not confirmed
    if (order_id and order_found and not payment_confirmed and 
    order_id not in verification_in_progress and 
    order_id not in verification_completed):
        print(f"🔍 Starting automatic payment verification for {order_id}...")
        verification_in_progress.add(order_id)  # Mark as verifying
        
        # Background status check after 3 seconds
        def check_status_delayed():
            import time
            try:
                print(f"📞 Verifying payment status for {order_id}...")
                
                for phone, job in sessions.items():
                    if job["order_data"]["order_id"] == order_id:
                        merchant_txn_id = job["order_data"].get("merchant_transaction_id")
                        current_status = job["order_data"].get("payment_status")
                        
                        # Skip if already confirmed
                        if current_status == "paid":
                            print(f"✅ Order {order_id} already confirmed")
                            return
                        
                        if merchant_txn_id:
                            from phonepe_payment import verify_payment
                            status_result = verify_payment(merchant_txn_id)
                            
                            if status_result['success']:
                                payment_state = status_result.get('state')
                                print(f"📊 Payment State: {payment_state}")
                                
                                if payment_state == "COMPLETED":
                                    # ✅ PAYMENT CONFIRMED
                                    job["order_data"]["payment_status"] = "paid"
                                    job["order_data"]["order_status"] = "confirmed"
                                    job["order_data"]["payment_completed_at"] = datetime.utcnow().isoformat()

                                    update_order_in_backend(
                                        order_id, 
                                        "paid", 
                                        "confirmed",
                                        shop_id=job.get("shop_id")  # e.g. SHOP_D2B55310
                                    )

                                    verification_completed[order_id] = "completed"

                                    transaction_id = status_result.get('transaction_id', 'N/A')
                                    job["order_data"]["phonepe_transaction_id"] = transaction_id
                                    
                                    # Save order
                                    server_path = ORDERS_DIR / f"{order_id}.json"
                                    with open(server_path, 'w') as f:
                                        json.dump(job["order_data"], f, indent=2)
                                    print(f"💾 Order confirmed: {server_path}")
                                    # Fetch printer config and print files
                                    shop_id = job.get("shop_id")
                                    printer_config = job.get("printer_config") or get_printer_config_for_shop(shop_id)
                                    if printer_config:
                                        print(f"🖨️ Sending {len(job['order_data']['files'])} file(s) to printer {printer_config['ip']}")
                                        for file_obj in job["order_data"]["files"]:
                                            local_path = file_obj.get("local_path")
                                            if local_path and os.path.exists(local_path):
                                                threading.Thread(
                                                    target=send_to_printer,
                                                    args=(
                                                        printer_config["ip"],
                                                        printer_config["port"],
                                                        printer_config["protocol"],
                                                        local_path
                                                    ),
                                                    daemon=True
                                                ).start()
                                            else:
                                                print(f"⚠️ File not found: {local_path}")
                                    else:
                                        print(f"⚠️ No printer config found for shop {shop_id}, skipping print")
                                        whatsapp_session = job.get("whatsapp_session_id")
                                        if whatsapp_session:
                                            send_whatsapp_text(
                                                phone,
                                                f"⚠️ *Printer Not Configured*\n\n"
                                                f"Order #{order_id} payment received ✅\n"
                                                f"But no printer is set up.\n\n"
                                                f"Please configure your printer in the dashboard and print manually.",
                                                session_id=whatsapp_session
                                            )
                                    
                                    # ✅ FIXED: Format price properly in WhatsApp message
                                    notification_key = f"{order_id}_success"
                                    if notification_key not in payment_notifications_sent:
                                        payment_notifications_sent.add(notification_key)
                                        
                                        summary = f"✅ *Order #{order_id} Confirmed!*\n\n"
                                        summary += f"💳 *Payment Successful* ✓\n"
                                        
                                        # ✅ FIXED: Format total price
                                        formatted_price = format_price(job['order_data']['total_price'])
                                        summary += f"Amount Paid: ₹{formatted_price}\n\n"
                                        
                                        for i, f in enumerate(job["order_data"]["files"], 1):
                                            opts = f['print_options']
                                            
                                            if opts["color"]:
                                                sides = "S"
                                                color = "C"
                                            else:
                                                sides = "S" if opts["sides"] == "single" else "D"
                                                color = "BW"
                                            
                                            sheets_info = f"{f['total_sheets']}sh" if 'total_sheets' in f else ""
                                            
                                            # ✅ FIXED: Format file price
                                            file_price = format_price(f['price'])
                                            
                                            summary += f"{i}. {f['filename']}\n"
                                            summary += f"   {f['page_count']}p|{sides}|{color}|{opts['copies']}x = {sheets_info} = ₹{file_price}\n"
                                        
                                        summary += f"\n📄 Total Pages: {job['order_data']['total_pages']}"
                                        
                                        if job['order_data'].get('total_sheets'):
                                            summary += f"\n📋 Total Sheets: {job['order_data']['total_sheets']}"
                                        
                                        # ✅ FIXED: Format total price again
                                        summary += f"\n💰 *Total: ₹{formatted_price}*"
                                        summary += f"\n🆔 Transaction: {transaction_id}"
                                        summary += f"\n\n🖨️ Your documents are being printed..."
                                        summary += f"\n📢 You'll be notified when ready for pickup!"
                                        
                                        whatsapp_session = job.get("whatsapp_session_id")
                                        if whatsapp_session:
                                            send_whatsapp_text(phone, summary, session_id=whatsapp_session)
                                            print(f"📱 Confirmation sent to {phone}")
                                        else:
                                            print(f"⚠️ No WhatsApp session for {phone}, skipping message (web-only order)")

                                        print(f"🔄 Resetting session for {phone} after successful payment")
                                        reset_session(phone)
                                    
                                elif payment_state == "FAILED":
                                    print(f"❌ Payment failed for {order_id}")
                                    job["order_data"]["payment_status"] = "failed"
                                    job["order_data"]["order_status"] = "cancelled"

                                    update_order_in_backend(
                                        order_id,
                                        "failed",      # ← correct
                                        "cancelled",   # ← correct
                                        shop_id=job.get("shop_id")
                                    )

                                    verification_completed[order_id] = "failed"

                                    server_path = ORDERS_DIR / f"{order_id}.json"
                                    with open(server_path, 'w') as f:
                                        json.dump(job["order_data"], f, indent=2)
                                    printer_config = job.get("printer_config")
                                    if printer_config:
                                        for file_obj in job["order_data"]["files"]:
                                            local_path = file_obj.get("local_path")
                                            if local_path and os.path.exists(local_path):
                                                threading.Thread(
                                                    target=send_to_printer,
                                                    args=(
                                                        printer_config["ip"],
                                                        printer_config["port"],
                                                        printer_config["protocol"],
                                                        local_path
                                                    ),
                                                    daemon=True
                                                ).start()
                                    
                                    notification_key = f"{order_id}_failed"
                                    if notification_key not in payment_notifications_sent:
                                        payment_notifications_sent.add(notification_key)
                                        
                                        whatsapp_session = job.get("whatsapp_session_id")
                                        if whatsapp_session:
                                            send_whatsapp_text(
                                                phone,
                                                f"❌ *Payment Failed*\n\n"
                                                f"Order #{order_id} cancelled\n\n"
                                                f"Please create a new order and try again.\n"
                                                f"Send 'hi' to start over.",
                                                session_id=whatsapp_session
                                            )
                                            print(f"📱 Failure notification sent to {phone}")
                                        else:
                                            print(f"⚠️ No WhatsApp session for {phone}, skipping failure message")
                                    print(f"🔄 Resetting session for {phone} after failed payment")
                                    reset_session(phone)

            finally:
                # ✅ CRITICAL: Remove from tracking when done
                verification_in_progress.discard(order_id)
        
        import threading
        thread = threading.Thread(target=check_status_delayed)
        thread.daemon = True
        thread.start()
    
    # ✅ CRITICAL FIX: Return different pages based on actual payment status
    if not order_found:
        # Order not found
        return """
        <!DOCTYPE html>
        <html>
        <head>
            <title>Order Not Found</title>
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <style>
                body {
                    font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                    display: flex;
                    justify-content: center;
                    align-items: center;
                    min-height: 100vh;
                    margin: 0;
                    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
                }
                .container {
                    background: white;
                    padding: 50px;
                    border-radius: 20px;
                    text-align: center;
                    box-shadow: 0 10px 40px rgba(0,0,0,0.3);
                }
                h1 { color: #e74c3c; }
            </style>
        </head>
        <body>
            <div class="container">
                <h1>❌ Order Not Found</h1>
                <p>This order does not exist or has expired.</p>
            </div>
        </body>
        </html>
        """
    
    elif payment_confirmed:
        # Payment is confirmed - show success page
        return f"""
        <!DOCTYPE html>
        <html>
        <head>
            <title>Payment Confirmed</title>
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <style>
                body {{
                    font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                    display: flex;
                    justify-content: center;
                    align-items: center;
                    min-height: 100vh;
                    margin: 0;
                    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
                }}
                .container {{
                    background: white;
                    padding: 50px;
                    border-radius: 20px;
                    text-align: center;
                    box-shadow: 0 10px 40px rgba(0,0,0,0.3);
                    max-width: 450px;
                }}
                .success-icon {{
                    font-size: 100px;
                    margin-bottom: 20px;
                    animation: bounce 1s ease;
                }}
                @keyframes bounce {{
                    0%, 100% {{ transform: translateY(0); }}
                    50% {{ transform: translateY(-20px); }}
                }}
                h1 {{
                    color: #10ac84;
                    margin-bottom: 15px;
                    font-size: 2rem;
                }}
                p {{
                    color: #666;
                    font-size: 1.1rem;
                    line-height: 1.6;
                }}
                .confirmed {{
                    background: #d4edda;
                    border: 2px solid #28a745;
                    color: #155724;
                    padding: 15px;
                    border-radius: 10px;
                    margin-top: 20px;
                    font-weight: bold;
                }}
                .info-box {{
                    background: #f8f9fa;
                    padding: 20px;
                    border-radius: 10px;
                    margin-top: 25px;
                    font-size: 0.9rem;
                    color: #555;
                }}
            </style>
        </head>
        <body>
            <div class="container">
                <div class="success-icon">✅</div>
                <h1>Payment Confirmed!</h1>
                <p>Thank you for your payment.</p>
                
                <div class="confirmed">✅ Order Confirmed! Check WhatsApp for details.</div>
                
                <div class="info-box">
                    <strong>📱 WhatsApp Confirmation Sent</strong><br>
                    Check your WhatsApp for order details.
                    <br><br>
                    <strong>🖨️ Printing Status</strong><br>
                    Your documents will be ready for pickup soon!
                </div>
            </div>
            
            <script>
                setTimeout(() => {{
                    window.close();
                }}, 5000);
            </script>
        </body>
        </html>
        """
    
    else:
        # Payment is still pending - show processing page
        return f"""
        <!DOCTYPE html>
        <html>
        <head>
            <title>Payment Processing</title>
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <style>
                body {{
                    font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                    display: flex;
                    justify-content: center;
                    align-items: center;
                    min-height: 100vh;
                    margin: 0;
                    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
                }}
                .container {{
                    background: white;
                    padding: 50px;
                    border-radius: 20px;
                    text-align: center;
                    box-shadow: 0 10px 40px rgba(0,0,0,0.3);
                    max-width: 450px;
                }}
                .success-icon {{
                    font-size: 100px;
                    margin-bottom: 20px;
                }}
                h1 {{
                    color: #f39c12;
                    margin-bottom: 15px;
                    font-size: 2rem;
                }}
                p {{
                    color: #666;
                    font-size: 1.1rem;
                    line-height: 1.6;
                }}
                .spinner {{
                    border: 3px solid #f3f3f3;
                    border-top: 3px solid #667eea;
                    border-radius: 50%;
                    width: 35px;
                    height: 35px;
                    animation: spin 1s linear infinite;
                    margin: 20px auto;
                }}
                @keyframes spin {{
                    0% {{ transform: rotate(0deg); }}
                    100% {{ transform: rotate(360deg); }}
                }}
                .loading {{
                    margin-top: 25px;
                    font-size: 0.95rem;
                    color: #999;
                }}
                .info-box {{
                    background: #fff3cd;
                    border: 2px solid #ffc107;
                    padding: 20px;
                    border-radius: 10px;
                    margin-top: 25px;
                    font-size: 0.9rem;
                    color: #856404;
                }}
            </style>
        </head>
        <body>
            <div class="container">
                <div class="success-icon">⏳</div>
                <h1>Processing Payment...</h1>
                <p>Please wait while we verify your payment.</p>
                
                <div class="spinner"></div>
                <p class="loading">Verifying payment status...</p>
                
                <div class="info-box">
                    <strong>⏰ Please Wait</strong><br>
                    This page will automatically update when payment is confirmed.
                    <br><br>
                    You'll receive a WhatsApp confirmation shortly.
                </div>
            </div>
            
            <script>
                // ✅ FIXED: Faster status checking
                let refreshCount = 0;
                const maxRefreshes = 10;  // Check for up to 50 seconds
                
                function checkPaymentStatus() {{
                    fetch('/api/order-status/{order_id}')
                        .then(response => response.json())
                        .then(data => {{
                            const status = data.order_data?.payment_status;
                            
                            if (status === 'paid') {{
                                // Payment confirmed - reload to show success page
                                location.reload();
                            }} else if (status === 'failed') {{
                                // Payment failed - show failure message immediately
                                document.querySelector('.success-icon').innerHTML = '❌';
                                document.querySelector('h1').innerHTML = 'Payment Failed';
                                document.querySelector('h1').style.color = '#e74c3c';
                                document.querySelector('p').innerHTML = 'Your payment could not be processed.';
                                document.querySelector('.spinner').style.display = 'none';
                                document.querySelector('.loading').innerHTML = 
                                    'Payment failed. Please close this window and try again.';
                                document.querySelector('.info-box').style.background = '#f8d7da';
                                document.querySelector('.info-box').style.border = '2px solid #f5c6cb';
                                document.querySelector('.info-box').innerHTML = 
                                    '<strong>❌ Payment Failed</strong><br>Please try again or contact support.';
                                
                                // Close window after 5 seconds
                                setTimeout(() => {{
                                    window.close();
                                }}, 5000);
                            }} else if (refreshCount < maxRefreshes) {{
                                // Still pending - check again faster
                                refreshCount++;
                                setTimeout(checkPaymentStatus, 2000);  // Check every 2 seconds
                            }} else {{
                                // Max retries reached
                                document.querySelector('.loading').innerHTML = 
                                    'Taking longer than expected. Please check WhatsApp for updates or close this window.';
                                setTimeout(() => {{
                                    window.close();
                                }}, 10000);
                            }}
                        }})
                        .catch(error => {{
                            console.error('Error checking status:', error);
                            if (refreshCount < maxRefreshes) {{
                                refreshCount++;
                                setTimeout(checkPaymentStatus, 2000);
                            }}
                        }});
                }}
                
                // Start checking immediately
                setTimeout(checkPaymentStatus, 500);
            </script>
        </body>
        </html>
        """

@app.route("/api/place-order", methods=["POST"])
def place_order():
    """Finalize order and generate payment link"""
    try:
        data = request.json
        session_id = data.get('session_id')
        
        # Find session
        job = None
        phone = None
        for p, sess in sessions.items():
            if sess.get("session_id") == session_id:
                job = sess
                phone = p
                break
        
        if not job:
            return jsonify({"success": False, "error": "Session not found"})
        
        # Check if order already placed
        if job.get("order_placed", False):
            return jsonify({
                "success": False, 
                "error": "Order already placed",
                "message": "This order has already been confirmed"
            })
        printer_config = data.get('printer_config')
        if printer_config:
            job["printer_config"] = printer_config

        # Validate files exist
        if not job["order_data"]["files"] or len(job["order_data"]["files"]) == 0:
            return jsonify({
                "success": False,
                "error": "No files in order"
            })
        
        # Mark order as placed
        job["order_placed"] = True
        
        # Calculate totals
        total_price = 0
        total_pages = 0
        total_sheets = 0
        
        for file_obj in job["order_data"]["files"]:
            pages = file_obj["page_count"]
            copies = file_obj["print_options"]["copies"]
            color = file_obj["print_options"]["color"]
            sides = file_obj["print_options"]["sides"]
            
            # Calculate sheets
            sheets = pages if sides == 'single' else math.ceil(pages / 2)
            total_sheets_file = sheets * copies
            
            # Calculate price
            rate = PRICING['sheet_color'] if color else PRICING['sheet_bw']
            price = total_sheets_file * rate
            
            file_obj["sheets_required"] = sheets
            file_obj["total_sheets"] = total_sheets_file
            file_obj["price"] = format_price(price)
            file_obj["processing_status"] = "completed"
            
            total_price += price
            total_pages += pages
            total_sheets += total_sheets_file
        
        job["order_data"]["total_price"] = format_price(total_price)
        job["order_data"]["total_pages"] = total_pages
        job["order_data"]["total_sheets"] = total_sheets
        
        # Set status
        job["order_data"]["order_status"] = "pending_payment"
        job["order_data"]["payment_status"] = "pending"
        job["order_data"]["order_initiated_at"] = datetime.utcnow().isoformat()
        
        order_id = job["order_data"]["order_id"]
        
        # PhonePe payment
        redirect_url_with_order = f"{PHONEPE_REDIRECT_URL}?order_id={order_id}"
        
        payment_response = initiate_payment(
            order_id=order_id,
            amount=total_price,
            user_phone=phone,
            callback_url=PHONEPE_CALLBACK_URL,
            redirect_url=redirect_url_with_order
        )

        if not payment_response['success']:
            return jsonify({
                "success": False,
                "error": f"Payment gateway error: {payment_response['error']}"
            })
        
        payment_url = payment_response['payment_url']
        phonepe_order_id = payment_response['order_id']
        merchant_transaction_id = payment_response['transaction_id']

        job["order_data"]["phonepe_order_id"] = phonepe_order_id
        job["order_data"]["payment_url"] = payment_url
        job["order_data"]["merchant_transaction_id"] = merchant_transaction_id
        
        # Save order locally
        server_path = ORDERS_DIR / f"{order_id}.json"
        with open(server_path, 'w') as f:
            json.dump(job["order_data"], f, indent=2)
        print(f"✅ Order saved locally: {server_path}")
        
        # ✅ ============ SUBMIT ORDER TO BACKEND DATABASE ============
        try:
            print(f"\n{'='*60}")
            print(f"📤 SUBMITTING ORDER TO BACKEND DATABASE")
            print(f"{'='*60}")
            print(f"Order ID: {order_id}")
            print(f"Shop ID: {job.get('shop_id')}")
            print(f"Shop DB ID: {job.get('shop_database_id')}")
            print(f"Customer: {phone}")
            print(f"Total: ₹{job['order_data']['total_price']}")
            print(f"{'='*60}\n")
            
            # Prepare order data for backend
            backend_order_data = {
                "order_id": order_id,
                "shop_id": job.get("shop_id"),  # e.g., SHOP_D2B55310
                "session_id": job["order_data"]["session_id"],
                "user_id": phone,
                "total_pages": job["order_data"]["total_pages"],
                "total_sheets": job["order_data"]["total_sheets"],
                "total_price": job["order_data"]["total_price"],
                "payment_status": job["order_data"]["payment_status"],
                "order_status": job["order_data"]["order_status"],
                "order_data": json.dumps(job["order_data"])
            }
            
            print(f"📦 Calling: {BACKEND_API_URL}/api/public/order/submit")
            
            backend_response = requests.post(
                f"{BACKEND_API_URL}/api/public/order/submit",
                headers={"X-Internal-Key": INTERNAL_API_KEY},
                json=backend_order_data,
                timeout=10
            )
            
            print(f"📊 Backend Response Status: {backend_response.status_code}")
            
            if backend_response.ok:
                backend_result = backend_response.json()
                print(f"✅ ORDER SUBMITTED TO BACKEND SUCCESSFULLY!")
                print(f"   Response: {backend_result}")
            else:
                print(f"⚠️ Backend submission failed: {backend_response.status_code}")
                print(f"   Response: {backend_response.text}")
                
        except Exception as submit_error:
            print(f"⚠️ Failed to submit to backend (order still saved locally):")
            print(f"   Error: {submit_error}")
            import traceback
            traceback.print_exc()
        # ✅ ============ END OF BACKEND SUBMISSION ============
        
        # Send WhatsApp message
        formatted_total = format_price(total_price)
        whatsapp_session = job.get("whatsapp_session_id")
        send_whatsapp_text(
            phone, 
            f"💳 *Complete Payment*\n\n"
            f"Order Total: ₹{formatted_total}\n"
            f"Payment Link: {payment_url}\n\n"
            f"⏰ Link expires in 15 minutes",
            session_id=whatsapp_session
        )
        
        print("\n" + "="*50)
        print(f"✅ ORDER CREATED: {order_id}")
        print(f"   Customer: {phone[-4:].rjust(10, '*')}")  # mask phone
        print(f"   Total: ₹{job['order_data']['total_price']}")
        print(f"   Files: {len(job['order_data']['files'])}")
        print("="*50 + "\n")

        # Only full dump in debug mode:
        if os.getenv('FLASK_DEBUG', 'false').lower() == 'true':
            print(json.dumps(job["order_data"], indent=2))
        
        return jsonify({
            "success": True,
            "payment_url": payment_url,
            "order_id": order_id,
            "phonepe_order_id": phonepe_order_id,
            "total_price": formatted_total,
            "message": "Complete payment to confirm order"
        })
        
    except Exception as e:
        print(f"❌ Place order error: {e}")
        import traceback
        traceback.print_exc()
        return jsonify({"success": False, "error": str(e)})

@app.route("/api/payment-callback", methods=["POST"])
def payment_callback():
    """Handle PhonePe payment callback"""
    try:
        callback_data = request.json
        print(f"\n{'='*60}")
        print(f"📥 PAYMENT CALLBACK RECEIVED")
        print(f"{'='*60}")
        print(f"   Callback keys: {list(callback_data.keys())}")
        if os.getenv('FLASK_DEBUG', 'false').lower() == 'true':
            print(json.dumps(callback_data, indent=2))
                
        base64_response = callback_data.get('response')
        decoded_response = base64.b64decode(base64_response).decode()
        response_data = json.loads(decoded_response)
        
        merchant_transaction_id = response_data['data']['merchantTransactionId']
        payment_state = response_data['data']['state']
        phonepe_transaction_id = response_data['data']['transactionId']
        
        order_id = merchant_transaction_id.split('_TXN')[0]
        
        print(f"\n💳 Order: {order_id}")
        print(f"Transaction: {merchant_transaction_id}")
        print(f"PhonePe TXN: {phonepe_transaction_id}")
        print(f"Status: {payment_state}")
        
        order_updated = False
        for phone, job in sessions.items():
            if job["order_data"]["order_id"] == order_id:
                if payment_state == "COMPLETED":
                    # Payment success
                    job["order_data"]["payment_status"] = "paid"
                    job["order_data"]["order_status"] = "confirmed"
                    job["order_data"]["payment_completed_at"] = datetime.utcnow().isoformat()
                    job["order_data"]["phonepe_transaction_id"] = phonepe_transaction_id
                    
                    update_order_in_backend(
                        order_id, 
                        "paid", 
                        "confirmed",
                        shop_id=job.get("shop_id")  # e.g. SHOP_D2B55310
                    )
                    
                    server_path = ORDERS_DIR / f"{order_id}.json"
                    with open(server_path, 'w') as f:
                        json.dump(job["order_data"], f, indent=2)

                    print(f"✅ Order CONFIRMED: {order_id}")
                    shop_id = job.get("shop_id")
                    printer_config = job.get("printer_config") or get_printer_config_for_shop(shop_id)
                    if printer_config:
                        print(f"🖨️ Sending {len(job['order_data']['files'])} file(s) to printer {printer_config['ip']}")
                        for file_obj in job["order_data"]["files"]:
                            local_path = file_obj.get("local_path")
                            if local_path and os.path.exists(local_path):
                                threading.Thread(
                                    target=send_to_printer,
                                    args=(
                                        printer_config["ip"],
                                        printer_config["port"],
                                        printer_config["protocol"],
                                        local_path
                                    ),
                                    daemon=True
                                ).start()
                    
                    notification_key = f"{order_id}_success"
                    if notification_key not in payment_notifications_sent:
                        payment_notifications_sent.add(notification_key)
                        
                        summary = f"✅ *Order #{order_id} Confirmed!*\n\n"
                        summary += f"*Payment Successful* ✓\n\n"

                        for i, f in enumerate(job["order_data"]["files"], 1):
                            opts = f['print_options']
                            
                            if opts["color"]:
                                sides = "S"
                                color = "C"
                            else:
                                sides = "S" if opts["sides"] == "single" else "D"
                                color = "BW"
                            
                            sheets_info = f"{f['total_sheets']}sh" if 'total_sheets' in f else ""
                            
                            # ✅ FIXED: Format file price
                            file_price = format_price(f['price'])
                            
                            summary += f"{i}. {f['filename']}\n"
                            summary += f"   {f['page_count']}p|{sides}|{color}|{opts['copies']}x = {sheets_info} = ₹{file_price}\n"

                        summary += f"\n📄 Total Pages: {job['order_data']['total_pages']}"

                        if job['order_data'].get('total_sheets'):
                            summary += f"\n📋 Total Sheets: {job['order_data']['total_sheets']}"

                        # ✅ FIXED: Format total price
                        formatted_total = format_price(job['order_data']['total_price'])
                        summary += f"\n💰 *Amount Paid: ₹{formatted_total}*"
                        summary += f"\n🆔 Transaction ID: {phonepe_transaction_id}"
                        summary += f"\n\n🖨️ Your documents are being printed..."
                        summary += f"\n📢 You'll be notified when ready for pickup!"
                        whatsapp_session = job.get("whatsapp_session_id")
                        if whatsapp_session:
                            send_whatsapp_text(phone, summary, session_id=whatsapp_session)
                            print(f"📱 Confirmation sent to {phone}")
                        else:
                            print(f"⚠️ No WhatsApp session for {phone}, skipping message (web-only order)")
                        reset_session(phone)
                elif payment_state == "FAILED":
                    # Payment failed
                    job["order_data"]["payment_status"] = "failed"
                    job["order_data"]["order_status"] = "cancelled"
                    job["order_data"]["payment_failed_at"] = datetime.utcnow().isoformat()

                    update_order_in_backend(
                        order_id,
                        "failed",      # ← correct
                        "cancelled",   # ← correct
                        shop_id=job.get("shop_id")
                    )

                    server_path = ORDERS_DIR / f"{order_id}.json"
                    with open(server_path, 'w') as f:
                        json.dump(job["order_data"], f, indent=2)
                    print(f"❌ Order cancelled: {order_id}")
                    
                    notification_key = f"{order_id}_failed"
                    if notification_key not in payment_notifications_sent:
                        payment_notifications_sent.add(notification_key)
                        
                        whatsapp_session = job.get("whatsapp_session_id")
                        if whatsapp_session:
                            send_whatsapp_text(
                                phone,
                                f"❌ *Payment Failed*\n\n"
                                f"Order #{order_id} cancelled\n\n"
                                f"Please try again or send 'hi' to start over.",
                                session_id=whatsapp_session
                            )
                            print(f"📱 Failure notification sent to {phone}")
                        else:
                            print(f"⚠️ No WhatsApp session for {phone}, skipping failure message")
                        print(f"📱 Failure notification sent to {phone}")
                    print(f"🔄 Resetting session for {phone} after callback failure")
                    reset_session(phone)
                order_updated = True
                break
        
        if not order_updated:
            print(f"⚠️ Order {order_id} not found")
        
        print(f"{'='*60}\n")
        return jsonify({"success": True, "status": "processed"})
        
    except Exception as e:
        print(f"❌ Callback error: {e}")
        import traceback
        traceback.print_exc()
        return jsonify({"success": False, "error": str(e)}), 500

@app.route("/orders")
def list_orders():
    # Simple key check
    key = request.headers.get('X-Api-Key') or request.args.get('api_key')
    if not ORDERS_API_KEY or key != ORDERS_API_KEY:
        return jsonify({"error": "Unauthorized"}), 401
    try:
        orders = []
        for file_path in ORDERS_DIR.glob("*.json"):
            with open(file_path, 'r') as f:
                orders.append(json.load(f))
        return jsonify({"orders": orders, "count": len(orders)}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/orders/<order_id>")
def get_order(order_id):
    key = request.headers.get('X-Api-Key') or request.args.get('api_key')
    if not ORDERS_API_KEY or key != ORDERS_API_KEY:
        return jsonify({"error": "Unauthorized"}), 401
    
    # ← Sanitize order_id to prevent path traversal
    safe_order_id = secure_filename(order_id)
    if safe_order_id != order_id or '/' in order_id or '\\' in order_id:
        return jsonify({"error": "Invalid order ID"}), 400
    
    try:
        file_path = ORDERS_DIR / f"{safe_order_id}.json"
        # Verify path is inside ORDERS_DIR
        if not str(file_path.resolve()).startswith(str(ORDERS_DIR.resolve())):
            return jsonify({"error": "Invalid order ID"}), 400
        with open(file_path, 'r') as f:
            order_data = json.load(f)
        return jsonify(order_data), 200
    except FileNotFoundError:
        return jsonify({"error": "Order not found"}), 404
    except Exception as e:
        return jsonify({"error": str(e)}), 500

if __name__ == "__main__":
    print("\n" + "="*60)
    print("🚀 WhatsApp Print Shop Bot Started!")
    print("="*60)
    print(f"📱 WhatsApp Webhook: {NGROK_URL}/webhook")
    print(f"🌐 Web Interface: {NGROK_URL}/order/<session_id>")
    print(f"📊 Orders API: {NGROK_URL}/orders")
    print("="*60 + "\n")
    
    app.run(
        port=5000,
        debug=os.getenv('FLASK_DEBUG', 'false').lower() == 'true',
        use_reloader=False
    )
