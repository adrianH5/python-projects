from fastapi import APIRouter
from api.app.v1.endpoints import executions, workflows, replays

api_router = APIRouter()
api_router.include_router(workflows.router, prefix="/workflows", tags=["workflows"])
api_router.include_router(executions.router, prefix="/executions", tags=["executions"])
api_router.include_router(replays.router, prefix="/replay", tags=["replays"])
