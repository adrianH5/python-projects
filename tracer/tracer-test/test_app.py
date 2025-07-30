"""
TraceLab test application demonstrating SDK usage.

This module demonstrates how to use the TraceLab SDK to trace
interactions with external services (SMS, email, calendar).
"""

import os
import time
from typing import Dict, Any

import requests
from tracelab_sdk import init, shutdown


SERVICE_URLS = {
    "twilio": os.environ.get("MOCK_TWILIO_URL", "http://localhost:5001"),
    "gmail": os.environ.get("MOCK_GMAIL_URL", "http://localhost:5002"),
    "calendar": os.environ.get("MOCK_CALENDAR_URL", "http://localhost:5003"),
}


class NotificationService:
    """Handles various notification services."""

    def send_sms(self, account_sid: str, message: str) -> Dict[str, Any]:
        """
        Send SMS notification via mock Twilio service.

        Args:
            account_sid: Twilio account SID
            message: SMS message content

        Returns:
            Response data from the service
        """
        endpoint = f"/2010-04-01/Accounts/{account_sid}/Messages.json"
        url = f"{SERVICE_URLS['twilio']}{endpoint}"

        payload = {"To": "+15558675309", "From": "+15017122661", "Body": message}

        print(f"Sending SMS: {message}")
        response = requests.post(url, json=payload)
        response.raise_for_status()
        print("SMS sent successfully.")

        return response.json()

    def send_email(self, subject: str, content: str) -> int:
        """
        Send email via mock Gmail service.

        Args:
            subject: Email subject line
            content: Email body content

        Returns:
            HTTP status code
        """
        url = f"{SERVICE_URLS['gmail']}/v3/mail/send"

        payload = {
            "personalizations": [{"to": [{"email": "test@example.com"}]}],
            "from": {"email": "receipts@tracelab.dev"},
            "subject": subject,
            "content": [{"type": "text/plain", "value": content}],
        }

        print(f"Sending email: {subject}")
        response = requests.post(url, json=payload)
        response.raise_for_status()
        print("Email sent successfully.")

        return response.status_code

    def schedule_meeting(self, calendar_id: str, summary: str) -> Dict[str, Any]:
        """
        Schedule meeting via mock Calendar service.

        Args:
            calendar_id: Calendar identifier
            summary: Meeting summary/title

        Returns:
            Response data from the service
        """
        url = f"{SERVICE_URLS['calendar']}/v3/calendars/{calendar_id}/events"

        payload = {
            "summary": summary,
            "start": {"dateTime": "2024-07-01T10:00:00-07:00"},
            "end": {"dateTime": "2024-07-01T11:00:00-07:00"},
        }

        print(f"Scheduling meeting: {summary}")
        response = requests.post(url, json=payload)
        response.raise_for_status()
        print("Meeting scheduled successfully.")

        return response.json()


def run_test_workflow() -> None:
    """Execute the test workflow with all notification types."""
    notification_service = NotificationService()

    # Send SMS notification
    notification_service.send_sms(
        account_sid="ACxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
        message="Your order has been shipped!",
    )

    # Send email receipt
    notification_service.send_email(
        subject="Your TraceLab Receipt", content="Thank you for your purchase."
    )

    # Schedule follow-up meeting
    notification_service.schedule_meeting(
        calendar_id="primary", summary="Follow-up on your recent order"
    )


def main() -> None:
    """Main entry point for the test application."""
    workflow_name = f"sample-test-run-{int(time.time())}"

    # Initialize TraceLab SDK
    init(
        workflow_name=workflow_name,
        service_name="my-test-app",
    )

    print("--- Starting TraceLab Test Run ---")

    try:
        run_test_workflow()

        print("\n--- Test Run Completed Successfully ---")
        print(f"You can now view the '{workflow_name}' workflow in the TraceLab UI.")

    except requests.exceptions.RequestException as e:
        print("\n--- An error occurred during the test run ---")
        print(e)
    finally:
        print("--- Shutting down TraceLab SDK ---")
        shutdown()


if __name__ == "__main__":
    main()
