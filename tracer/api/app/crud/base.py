"""
Base CRUD operations for database models.

This module provides a generic base class for Create, Read, Update,
and Delete operations that can be inherited by specific model CRUDs.
"""

from typing import Any, Dict, Generic, List, Optional, Type, TypeVar, Union

from pydantic import BaseModel
from sqlalchemy.orm import Session

from api.app.db.base_class import Base

ModelType = TypeVar("ModelType", bound=Base)
CreateSchemaType = TypeVar("CreateSchemaType", bound=BaseModel)
UpdateSchemaType = TypeVar("UpdateSchemaType", bound=BaseModel)


class CRUDBase(Generic[ModelType, CreateSchemaType, UpdateSchemaType]):
    """
    Base class for CRUD operations on a database model.

    Attributes:
        model: SQLAlchemy model class
    """

    def __init__(self, model: Type[ModelType]):
        """
        Initialize CRUD object with a model class.

        Args:
            model: SQLAlchemy model class
        """
        self.model = model

    def get(self, db: Session, id: Any) -> Optional[ModelType]:
        """
        Get a single record by ID.

        Args:
            db: Database session
            id: Record ID

        Returns:
            Model instance or None if not found
        """
        return db.query(self.model).filter(self.model.id == id).first()

    def get_multi(
        self, db: Session, *, skip: int = 0, limit: int = 100
    ) -> List[ModelType]:
        """
        Get multiple records with pagination.

        Args:
            db: Database session
            skip: Number of records to skip
            limit: Maximum number of records to return

        Returns:
            List of model instances
        """
        return db.query(self.model).offset(skip).limit(limit).all()

    def create(
        self, db: Session, *, obj_in: CreateSchemaType, commit: bool = True
    ) -> ModelType:
        """
        Create a new record in the database.

        Args:
            db: Database session
            obj_in: Pydantic schema with creation data
            commit: Whether to commit the transaction

        Returns:
            Created model instance
        """
        obj_data = obj_in.dict()
        db_obj = self.model(**obj_data)

        db.add(db_obj)

        if commit:
            db.commit()
            db.refresh(db_obj)
        else:
            db.flush()
            db.refresh(db_obj)

        return db_obj

    def update(
        self,
        db: Session,
        *,
        db_obj: ModelType,
        obj_in: Union[UpdateSchemaType, Dict[str, Any]],
        commit: bool = True
    ) -> ModelType:
        """
        Update an existing record.

        Args:
            db: Database session
            db_obj: Existing model instance to update
            obj_in: Update data as Pydantic schema or dictionary
            commit: Whether to commit the transaction

        Returns:
            Updated model instance
        """
        if isinstance(obj_in, dict):
            update_data = obj_in
        else:
            update_data = obj_in.dict(exclude_unset=True)

        for field, value in update_data.items():
            if hasattr(db_obj, field):
                setattr(db_obj, field, value)

        db.add(db_obj)

        if commit:
            db.commit()
            db.refresh(db_obj)

        return db_obj

    def remove(
        self, db: Session, *, id: int, commit: bool = True
    ) -> Optional[ModelType]:
        """
        Delete a record by ID.

        Args:
            db: Database session
            id: Record ID to delete
            commit: Whether to commit the transaction

        Returns:
            Deleted model instance or None if not found
        """
        obj = db.query(self.model).get(id)

        if obj is None:
            return None

        db.delete(obj)

        if commit:
            db.commit()

        return obj
