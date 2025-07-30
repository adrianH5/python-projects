from sqlalchemy.orm import Session
from api.app.db import Base  # noqa: F401
from api.app.db.session import engine

# make sure all SQL Alchemy models are imported (app.db.base) before initializing DB
# otherwise, SQL Alchemy might fail to initialize relationships properly
# for more details: https://github.com/tiangolo/full-stack-fastapi-postgresql/issues/28


def init_db(db: Session) -> None:
    # TODO: Use Alembic for migrations instead of creating tables directly.
    Base.metadata.create_all(bind=engine)
