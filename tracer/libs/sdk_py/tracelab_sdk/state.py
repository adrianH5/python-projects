"""
Global state management for TraceLab SDK.

This module maintains the SDK's runtime state including
Redis connection, workflow configuration, and hooks.
"""

from typing import Dict, Optional, Any
import redis


class SDKState:
    """Container for SDK global state."""

    def __init__(self):
        self.redis_client: Optional[redis.Redis] = None
        self.workflow_name: Optional[str] = None
        self.service_name: Optional[str] = None
        self.run_id: Optional[str] = None
        self.tags: Dict[str, Any] = {}
        self.hooks: Dict[str, Dict[str, Any]] = {}
        self.step_index: int = 0

    def increment_step(self) -> int:
        """Increment and return the step index."""
        self.step_index += 1
        return self.step_index

    def reset(self) -> None:
        """Reset all state to initial values."""
        if self.redis_client:
            self.redis_client.close()

        self.__init__()


# Global state instance
_state = SDKState()

# Expose state attributes at module level for backward compatibility
redis_client = property(lambda: _state.redis_client)
workflow_name = property(lambda: _state.workflow_name)
service_name = property(lambda: _state.service_name)
run_id = property(lambda: _state.run_id)
tags = property(lambda: _state.tags)
hooks = property(lambda: _state.hooks)


# Allow direct attribute access
def __getattr__(name):
    return getattr(_state, name)


def __setattr__(name, value):
    if name.startswith("_"):
        globals()[name] = value
    else:
        setattr(_state, name, value)
