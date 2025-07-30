from pydantic import BaseModel
from typing import Literal, Optional


class ReplayCreate(BaseModel):
    mode: Literal["deterministic", "chaos"]
    chaos_config: Optional[dict] = None
