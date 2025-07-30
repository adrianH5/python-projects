from pydantic_settings import BaseSettings


class Settings(BaseSettings):
    PROJECT_NAME: str = "TraceLab"
    API_V1_STR: str = "/api/v1"
    DATABASE_URL: str = "postgresql://trace:trace@postgres/trace"
    REDIS_URL: str = "redis://redis:6379/0"

    class Config:
        case_sensitive = True


settings = Settings()
