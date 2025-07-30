FROM python:3.12-slim

WORKDIR /app

RUN pip install flask

COPY app.py /app/

CMD ["flask", "run", "--host=0.0.0.0"]
