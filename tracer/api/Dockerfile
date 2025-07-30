FROM python:3.12-slim

WORKDIR /app

RUN pip install poetry

# Copy only the dependency definitions to leverage Docker layer caching
COPY api/pyproject.toml /app/

RUN rm -f poetry.lock && poetry config virtualenvs.create false && poetry install --without dev --no-root

COPY . /app

# The app path is now api.app.main because the build context is the project root.
CMD ["uvicorn", "api.app.main:app", "--host", "0.0.0.0", "--port", "8000"]
