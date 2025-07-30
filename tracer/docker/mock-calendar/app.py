from flask import Flask, jsonify

app = Flask(__name__)


@app.route("/v3/calendars/<calendar_id>/events", methods=["POST"])
def create_event(calendar_id):
    return jsonify({"id": "evt_xxxxxxxx", "status": "confirmed"})


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000)
