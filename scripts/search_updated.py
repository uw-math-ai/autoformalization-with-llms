from abc import abstractmethod
import heapq
from typing import Any, Callable, Dict, List, Optional, Tuple
import unittest
from pantograph.expr import Expr, Tactic, GoalState
from pantograph.server import Server, TacticFailure, ServerError


class SearchState:
    """
    A class representing a state in the search space.
    """
    
    goal_state: GoalState
    parent: Optional["SearchState"]
    parent_goal_id: Optional[int]
    priorities: list[float]
    children: Optional[List["SearchState"]] = None
    tested_tactics: Optional[List[Tactic]] = None
    total_value: Optional[float] = None
    tactic_feedback: Optional[str] = None

    def __post_init__(self):
        assert len(self.priorities) == len(self.goal_state.goals)
        self.solved = [False for _ in self.goal_state.goals]
        self.trials = [0 for _ in self.goal_state.goals]
        self.tested_tactics = [] if self.tested_tactics is None else self.tested_tactics
        self.children = [] if self.children is None else self.children
        self.visit_count = 1
        self.exhausted = False
        self.subtree_exhausted = False

    def __eq__(self, other):
        return self.goal_state == other.goal_state
    
    def __str__(self):
        return f"SearchState(goal_state={self.goal_state}, " \
            f"parent_goal_id={self.parent_goal_id}, " \
            f"priorities={self.priorities}, solved={self.solved})"

    @property
    def next_goal_id(self) -> int:
        goal_id, _ = max(
            ((i, prio) for i, prio in enumerate(self.priorities) if not self.solved[i]),
            key=lambda x: x[1])
        return goal_id

    @property
    def is_root(self) -> bool:
        return self.parent is None

    @property
    def is_solved(self) -> bool:
        return all(self.solved)


class Step:
    """
    A class representing a step in the search process.
    """

    state: SearchState
    tactic: Tactic

    def __str__(self):
        return f"Step(state={self.state}, tactic={self.tactic})"


class SearchResult:
    """
    A class representing the result of a search.
    """

    root_state: SearchState
    duration: float
    solve: bool
    steps: Optional[List[Step]] = None

    def __str__(self):
        return f"SearchResult(root_state={self.root_state}, " \
            f"duration={self.duration}, solve={self.solve}, steps={self.steps})"


class SearchAgent():
    """
    A class representing a search agent.
    """

    @abstractmethod
    def step_candidates(
            self,
            state: GoalState,
            goal_id: int,
        ) -> Optional[Tactic]:
        """
        Implement this function to generate the next tactic for a goal
        """

    @abstractmethod
    def guidance(self, state: GoalState) -> list[float]:
        """
        Return a list of priorities determining which goal should be searched
        first. This will not be called on states with one or zero goals.
        """
        return [0.0 for _ in state.goals]
    
    @abstractmethod
    def reset(self):
        """
        Called after search
        """

    @abstractmethod
    def search(self,
               server: Server,
               goal_state: GoalState,
               max_steps: int = 100,
               max_trials_per_goal: int = 5,
               verbose: bool = False) -> SearchResult:
        """
        Executes proof search on this state
        """
        return SearchResult(
            root_state=SearchState(
                goal_state=goal_state,
                parent=None,
                priorities=self.guidance(goal_state),
            ),
            duration=0.0,
            solve=False,
        )
