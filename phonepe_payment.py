"""
PhonePe Payment Gateway Integration Module
Handles OAuth authentication and payment initiation
"""

import os
import re
import time
import hmac
import logging
import hashlib
import threading
import requests
import json
from datetime import datetime, timedelta
from dotenv import load_dotenv

load_dotenv()

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# ============ CONFIGURATION ============
PHONEPE_CLIENT_ID     = os.getenv("PHONEPE_CLIENT_ID")
PHONEPE_CLIENT_SECRET = os.getenv("PHONEPE_CLIENT_SECRET")
PHONEPE_MERCHANT_ID   = os.getenv("PHONEPE_MERCHANT_ID")

if not all([PHONEPE_CLIENT_ID, PHONEPE_CLIENT_SECRET, PHONEPE_MERCHANT_ID]):
    raise RuntimeError("Missing required PhonePe credentials in environment variables")

PHONEPE_ENV = os.getenv("PHONEPE_ENV", "sandbox")  # "sandbox" or "production"

if PHONEPE_ENV == "production":
    PHONEPE_OAUTH_URL   = "https://api.phonepe.com/apis/pg/v1/oauth/token"
    PHONEPE_PAY_API_URL = "https://api.phonepe.com/apis/pg/checkout/v2/pay"
    PHONEPE_STATUS_BASE = "https://api.phonepe.com/apis/pg/payments/v2/order"
else:
    PHONEPE_OAUTH_URL   = "https://api-preprod.phonepe.com/apis/pg-sandbox/v1/oauth/token"
    PHONEPE_PAY_API_URL = "https://api-preprod.phonepe.com/apis/pg-sandbox/checkout/v2/pay"
    PHONEPE_STATUS_BASE = "https://api-preprod.phonepe.com/apis/pg-sandbox/payments/v2/order"

# Token storage (in-memory cache)
_access_token = None
_token_expiry = None
# FIX: lock to prevent race condition on concurrent token refresh
_token_lock = threading.Lock()


def get_access_token():
    """
    Get OAuth access token with caching.
    Returns: access_token string or None if failed.
    """
    global _access_token, _token_expiry

    # FIX: serialize token refresh so only one thread fetches at a time
    with _token_lock:
        if _access_token and _token_expiry and datetime.now() < _token_expiry:
            print("✓ Using cached PhonePe token")
            return _access_token

        print("\n🔐 Getting new PhonePe OAuth token...")

        auth_attempts = [
            {
                "client_id": PHONEPE_CLIENT_ID,
                "client_secret": PHONEPE_CLIENT_SECRET,
                "client_version": "1",
                "grant_type": "client_credentials"
            },
            {
                "client_id": PHONEPE_CLIENT_ID,
                "client_secret": PHONEPE_CLIENT_SECRET,
                "grant_type": "client_credentials"
            }
        ]

        headers = {"Content-Type": "application/x-www-form-urlencoded"}

        for attempt_num, data in enumerate(auth_attempts, 1):
            print(f"📤 OAuth Attempt {attempt_num}...")

            try:
                response = requests.post(
                    PHONEPE_OAUTH_URL,
                    headers=headers,
                    data=data,
                    timeout=10
                )

                print(f"   Status: {response.status_code}")

                if response.status_code == 200:
                    token_data = response.json()
                    _access_token = token_data.get("access_token")
                    expires_in = token_data.get("expires_in", 3600)

                    # Set expiry with 5-minute buffer
                    _token_expiry = datetime.now() + timedelta(seconds=expires_in - 300)

                    print(f"✅ Token obtained! Expires in {expires_in}s")
                    return _access_token

            except Exception as e:
                print(f"❌ Attempt {attempt_num} failed: {e}")
                continue

        print("❌ All OAuth attempts failed!")
        return None


def validate_phonepe_callback(request_body, x_verify_header):
    """
    Validate PhonePe callback using X-Verify header.

    Args:
        request_body (str): Raw request body as string
        x_verify_header (str): X-Verify header value (format: hash###saltIndex)

    Returns:
        bool: True if valid, False otherwise
    """
    try:
        parts = x_verify_header.split('###')
        if len(parts) < 1:
            print("❌ Malformed X-Verify header")
            return False

        received_hash = parts[0]

        SALT_KEY = os.getenv("PHONEPE_SALT_KEY")
        if not SALT_KEY:
            print("❌ PHONEPE_SALT_KEY not set — cannot validate callback")
            return False

        # FIX: correct hash formula for callbacks is SHA256(body + salt_key)
        # The endpoint string is only used for outbound request signing, not callbacks
        expected_string = request_body + SALT_KEY
        expected_hash = hashlib.sha256(expected_string.encode()).hexdigest()

        # FIX: use constant-time comparison to prevent timing attacks
        is_valid = hmac.compare_digest(received_hash.lower(), expected_hash.lower())

        if is_valid:
            print("✅ X-Verify validation successful")
        else:
            print("❌ Hash mismatch — callback validation failed")

        return is_valid

    except Exception as e:
        print(f"❌ X-Verify validation error: {e}")
        return False


def initiate_payment(order_id, amount, user_phone, callback_url, redirect_url):
    """
    Initiate PhonePe payment for an order.

    Args:
        order_id (str): Unique order identifier
        amount (float): Payment amount in rupees
        user_phone (str): Customer's phone number
        callback_url (str): URL for payment status callbacks
        redirect_url (str): URL to redirect after payment

    Returns:
        dict: {
            "success": bool,
            "payment_url": str (if success),
            "order_id": str (PhonePe order ID),
            "error": str (if failed)
        }
    """

    token = get_access_token()
    if not token:
        return {
            "success": False,
            "error": "Failed to get OAuth token. Check PhonePe credentials."
        }

    # FIX: import time moved to top of file
    merchant_transaction_id = f"{order_id}_TXN{int(time.time())}"

    payment_data = {
        "merchantOrderId": merchant_transaction_id,
        "amount": int(amount * 100),  # Convert to paise
        "paymentFlow": {
            "type": "PG_CHECKOUT",
            "merchantUrls": {
                "redirectUrl": redirect_url,
                "callbackUrl": callback_url
            }
        }
    }

    print("\n💳 INITIATING PAYMENT:")
    print(f"   Order: {order_id}")
    print(f"   Amount: ₹{amount}")
    print(f"   Transaction ID: {merchant_transaction_id}")
    print(f"   User: {user_phone}")

    # CRITICAL: PhonePe uses "O-Bearer" not "Bearer"
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"O-Bearer {token}"
    }

    try:
        response = requests.post(
            PHONEPE_PAY_API_URL,
            json=payment_data,
            headers=headers,
            timeout=15
        )

        print(f"📥 Response Status: {response.status_code}")

        if response.status_code in [200, 201]:
            response_data = response.json()

            phonepe_order_id = response_data.get("orderId")
            state            = response_data.get("state")
            payment_url      = response_data.get("redirectUrl")
            expire_at        = response_data.get("expireAt")

            if payment_url and phonepe_order_id:
                print("✅ PAYMENT LINK GENERATED!")
                print(f"   Payment URL: {payment_url}")
                print(f"   PhonePe Order ID: {phonepe_order_id}")
                print(f"   State: {state}")
                print(f"   Expires: {expire_at}")

                return {
                    "success": True,
                    "payment_url": payment_url,
                    "order_id": phonepe_order_id,
                    "transaction_id": merchant_transaction_id,
                    "state": state,
                    "expire_at": expire_at
                }
            else:
                print("❌ Missing payment URL or order ID in response")
                return {
                    "success": False,
                    "error": "Invalid response from PhonePe (missing payment URL)",
                    "response": response_data
                }

        else:
            try:
                error_data = response.json()
                error_msg  = error_data.get("response", {}).get("message", "Unknown error")
                error_code = error_data.get("response", {}).get("errorCode", "N/A")

                print(f"❌ PhonePe Error: {error_code} - {error_msg}")

                return {
                    "success": False,
                    "error": f"PhonePe Error: {error_msg} (Code: {error_code})",
                    "error_code": error_code,
                    "response": error_data
                }
            # FIX: bare except replaced with specific exception types
            except (ValueError, KeyError):
                print(f"❌ HTTP Error: {response.status_code}")
                return {
                    "success": False,
                    "error": f"Payment gateway error: HTTP {response.status_code}",
                    "response": response.text
                }

    except requests.exceptions.Timeout:
        print("❌ Request timeout")
        return {
            "success": False,
            "error": "Payment gateway timeout. Please try again."
        }
    except requests.exceptions.ConnectionError:
        print("❌ Connection error")
        return {
            "success": False,
            "error": "Cannot connect to payment gateway. Check internet connection."
        }
    except Exception as e:
        # FIX: replaced traceback.print_exc() with logger to avoid leaking internals
        logger.exception("Unexpected error in initiate_payment")
        return {
            "success": False,
            "error": f"Payment initiation failed: {str(e)}"
        }


def verify_payment(merchant_transaction_id):
    """
    Verify payment status with PhonePe.

    Args:
        merchant_transaction_id (str): YOUR merchant transaction ID (e.g., ORD_XXX_TXN123)
                                       NOT the PhonePe order ID

    Returns:
        dict: Payment status details
    """

    print(f"\n{'='*60}")
    print(f"🔍 VERIFYING PAYMENT STATUS")
    print(f"{'='*60}")
    print(f"Merchant Transaction ID: {merchant_transaction_id}")

    # FIX: validate transaction ID before interpolating into URL (SSRF prevention)
    if not re.match(r'^[a-zA-Z0-9_-]{1,64}$', str(merchant_transaction_id)):
        return {"success": False, "error": "Invalid transaction ID format"}

    token = get_access_token()
    if not token:
        print("❌ Failed to get OAuth token")
        return {
            "success": False,
            "error": "Failed to get OAuth token"
        }

    print(f"✅ OAuth token obtained")

    status_url = f"{PHONEPE_STATUS_BASE}/{merchant_transaction_id}/status"
    print(f"📞 Calling: {status_url}")

    headers = {
        "Content-Type": "application/json",
        "Authorization": f"O-Bearer {token}"
    }

    try:
        response = requests.get(status_url, headers=headers, timeout=10)

        print(f"📥 Response Status: {response.status_code}")
        # FIX: do not log full response body — may contain PII
        print(f"📥 Response received ({len(response.text)} bytes)")

        if response.status_code == 200:
            status_data = response.json()

            order_id        = status_data.get("orderId")
            state           = status_data.get("state")
            amount          = status_data.get("amount", 0)
            expire_at       = status_data.get("expireAt")

            transaction_id  = None
            payment_details = status_data.get("paymentDetails", [])
            if payment_details and len(payment_details) > 0:
                transaction_id = payment_details[0].get("transactionId")

            print(f"✅ Payment State: {state}")
            print(f"   PhonePe Order ID: {order_id}")
            print(f"   Amount: ₹{amount / 100}")
            print(f"   Transaction ID: {transaction_id}")
            print(f"   Expires At: {expire_at}")
            print(f"{'='*60}\n")

            return {
                "success": True,
                "state": state,
                "phonepe_order_id": order_id,
                "amount": amount / 100,  # Convert paise to rupees
                "transaction_id": transaction_id,
                "expire_at": expire_at,
                "response": status_data
            }

        elif response.status_code == 404:
            print(f"⚠️  Order not found - payment might still be processing")
            return {
                "success": False,
                "error": "Order not found (might still be processing)",
                "state": "PENDING"
            }

        else:
            try:
                error_data = response.json()
                error_msg  = error_data.get("message", "Unknown error")
                print(f"❌ Status check failed: {error_msg}")
            # FIX: bare except replaced with specific exception types
            except (ValueError, KeyError):
                error_msg = response.text
                print(f"❌ Status check failed: {error_msg}")

            print(f"{'='*60}\n")

            return {
                "success": False,
                "error": f"Status check failed: {response.status_code} - {error_msg}",
                "response": response.text
            }

    except requests.exceptions.Timeout:
        print("❌ Request timeout")
        print(f"{'='*60}\n")
        return {
            "success": False,
            "error": "Status check timeout - PhonePe API not responding"
        }

    except requests.exceptions.ConnectionError:
        print("❌ Connection error - cannot reach PhonePe API")
        print(f"{'='*60}\n")
        return {
            "success": False,
            "error": "Cannot connect to PhonePe API"
        }

    except Exception as e:
        # FIX: replaced traceback.print_exc() with logger
        logger.exception("Unexpected error in verify_payment")
        print(f"{'='*60}\n")
        return {
            "success": False,
            "error": f"Unexpected error: {str(e)}"
        }


# Test function (optional - for debugging)
if __name__ == "__main__":
    print("\n" + "="*60)
    print("🔧 PHONEPE PAYMENT MODULE TEST")
    print("="*60)
    # FIX: mask sensitive credential in output, merchant ID is non-secret
    print(f"Client ID: {'*' * (len(PHONEPE_CLIENT_ID) - 4)}{PHONEPE_CLIENT_ID[-4:]}")
    print(f"Merchant ID: {PHONEPE_MERCHANT_ID}")
    print("="*60 + "\n")

    print("Testing OAuth...")
    token = get_access_token()

    if token:
        # FIX: do not print any portion of the token
        print(f"\n✅ OAuth Success!")

        print("\n\nTesting Payment Initiation...")
        result = initiate_payment(
            order_id="TEST_ORDER_001",
            amount=10.00,
            user_phone="919999999999",
            callback_url="https://example.com/callback",
            redirect_url="https://example.com/success"
        )

        print("\n" + "="*60)
        print("RESULT:")
        print(json.dumps(result, indent=2))
        print("="*60)
    else:
        print("\n❌ OAuth Failed!")
        print("Check your PhonePe credentials in .env file")