from flask import Flask, jsonify

app = Flask(__name__)


@app.route("/v3/mail/send", methods=["POST"])
def send_mail():
    return jsonify({}), 202


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5000)
