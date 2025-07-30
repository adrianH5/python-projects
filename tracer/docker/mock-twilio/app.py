from flask import Flask, jsonify

app = Flask(__name__)


@app.route("/2010-04-01/Accounts/<account_sid>/Messages.json", methods=["POST"])
def create_message(account_sid):
    return jsonify({"sid": "SMxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "status": "queued"})


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000)
