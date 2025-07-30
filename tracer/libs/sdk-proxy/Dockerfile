FROM mitmproxy/mitmproxy

RUN pip install redis
COPY proxy.py /app/proxy.py
CMD ["mitmweb", "--web-host", "0.0.0.0", "--listen-port", "8888", "-s", "/app/proxy.py"]
