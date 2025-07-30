FROM python:3.11-slim

# Set environment variables
ENV PYTHONDONTWRITEBYTECODE 1
ENV PYTHONUNBUFFERED 1
ENV PYTHONPATH /code

# Set the working directory in the container
WORKDIR /code

# Install system dependencies required by Playwright and other libraries
# Playwright requires certain browser dependencies.
RUN apt-get update && apt-get install -y --no-install-recommends \
  curl \
  build-essential \
  && rm -rf /var/lib/apt/lists/*

# Copy the requirements file into the container at /code
COPY ./requirements.txt /code/requirements.txt

# Using --no-cache-dir to reduce image size
RUN pip install --no-cache-dir --upgrade pip
RUN pip install --no-cache-dir -r requirements.txt

# Install Playwright browsers
# This command downloads the browser binaries.
RUN playwright install chromium --with-deps
# If the above fails due to needing specific browsers, you can specify:
# RUN playwright install chromium firefox webkit --with-deps

# Copy the 'app' directory from the build context (which is 'backend/')
# into '/code/app' in the image.
# This ensures backend/app/main.py becomes /code/app/main.py.
COPY app /code/app

EXPOSE 8000

CMD ["uvicorn", "app.main:app", "--host", "0.0.0.0", "--port", "8000"]
