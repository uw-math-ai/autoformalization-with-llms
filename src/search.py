from abc import ABC, abstractmethod
import heapq
from typing import List, Tuple, Optional, Dict

from pantograph.expr import Expr, Tactic, GoalState, Goal
from pantograph.server import Server, TacticFailure, ServerError
import torch
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM
from transformers.generation.utils import GenerateBeamEncoderDecoderOutput


class AStarSearchState():
    """
    An implementation of the SearchState interface.
    Represents a state in the A* search algorithm.
    """

    goal_state: GoalState
    priorities: list[float]
    generator_score: float
    parent: Optional['AStarSearchState']
    parent_goal_id: Optional[int]
    
    def __init__(self, goal_state, priorities=None, generator_score=None, parent=None, parent_goal_id=None):
        self.goal_state = goal_state
        self.priorities = priorities if priorities is not None else [0.0] * len(goal_state.goals)
        self.generator_score = generator_score if generator_score is not None else 0.0
        self.parent = parent
        self.parent_goal_id = parent_goal_id

    def update_priorities(self, priorities):
        self.priorities = priorities
    
    @property
    def next_goal_id(self) -> int:
        goal_id, _ = max(
            ((i, prio) for i, prio in enumerate(self.priorities)),
            key=lambda x: x[1])
        return goal_id
    
    @property  
    def is_terminal(self):
        return self.goal_state.is_solved
    
    def __str__(self):
        return f"AStarSearchState(goal_state={self.goal_state}, generator_score={self.generator_score}, priorities={self.priorities})"
    
    def __lt__(self, other):
        return self.generator_score < other.generator_score
    
    def __eq__(self, other):
        return isinstance(other, AStarSearchState) and self.goal_state == other.goal_state
    
    def __hash__(self):
        return hash(self.goal_state.state_id)


class AStarSearchAction():
    """
    An implementation of the SearchAction interface.
    Represents an action in the A* search algorithm.
    """

    applied_state: AStarSearchState
    goal_id: int
    tactic: Tactic
    generator_score: float
    result_state: Optional[AStarSearchState]
    feedback: Optional[str]


    def __init__(self, applied_state, goal_id, tactic, generator_score=None, result_state=None, feedback=None):
        self.applied_state = applied_state
        self.goal_id = goal_id
        self.tactic = tactic
        self.generator_score = generator_score if generator_score is not None else 0.0
        self.result_state = result_state
        self.feedback = feedback

    def update_result_state(self, result_state, feedback=None):
        self.result_state = result_state
        self.feedback = feedback

    def __str__(self):
        return f"AStarSearchAction(tactic={str(self.tactic)}, generator_score={self.generator_score})"
    
    def to_code(self):
        """
        Convert the action to a string representation.
        """
        return str(self.tactic)


class DojoModel():
    """
    A generation model that uses LeanDojo
    """
    device: str
    model: AutoModelForSeq2SeqLM
    tokenizer: AutoTokenizer
    generate_config: dict

    def __init__(self, device: str = None, generate_config: dict = None):
        """
        Initializes the wrapper by loading the model and tokenizer.
        """
        model_name = "kaiyuy/leandojo-lean4-tacgen-byt5-small"
        self.device = device or ("cuda" if torch.cuda.is_available() else "cpu")
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        self.model = AutoModelForSeq2SeqLM.from_pretrained(model_name)
        self.model.to(self.device)
        self.generate_config = {
            "max_length": 1024,
            "num_beams": 15,
            "length_penalty": 0.0,
            "do_sample": True,
            "num_return_sequences": 10,
            "early_stopping": False,
            "output_scores": True,
            "return_dict_in_generate": True,
            "temperature": 1.0,
        }
        if generate_config:
            self.generate_config.update(generate_config)

    # TODO: Need to test different proof states
    def format_prompt(self, current_state: AStarSearchState) -> str:
        """
        Formats the prompt for the model based on the goal to solve.
        """
        goal = current_state.goal_state.goals[current_state.next_goal_id]
        prompt = str(goal)
        
        return prompt

    def generate(self, prompt: str, **generate_config) -> str:
        """
        Generates text based on the provided prompt.
        """
        config = self.generate_config.copy()
        config.update(generate_config)

        inputs = self.tokenizer(prompt, return_tensors='pt').to(self.device)
        outputs = self.model.generate(inputs.input_ids, **config)
        return outputs

    # TODO: Need to handle special tactics: have, let, calc
    def format_output(self, current_state: AStarSearchState, outputs: GenerateBeamEncoderDecoderOutput) \
            -> List[AStarSearchAction]:
        """
        Formats the generated text into the desired output structure.
        """
        actions = []

        for i, seq in enumerate(outputs.sequences):
            tactic = self.tokenizer.decode(seq, skip_special_tokens=True)
            if tactic.startswith("have") or tactic.startswith("let") or tactic.startswith("calc"):
                continue
            seq_score = -(outputs.sequences_scores[i].item())
            action = AStarSearchAction(current_state, current_state.next_goal_id, tactic, seq_score)
            actions.append(action)

        return actions

    def generate_actions(self, current_state: AStarSearchState, **generate_config) \
          -> List[AStarSearchAction]:
        prompt = self.format_prompt(current_state)
        raw_output = self.generate(prompt, **generate_config)
        return self.format_output(current_state, raw_output)
    

class PantographEnvironment():
    """
    An environment that uses Pantograph to apply actions to a state.
    """
    server: Server

    def __init__(self, server):
        self.server = server

    def step(self, state: AStarSearchState, goal_id: int, action: AStarSearchAction, actions: List[AStarSearchAction]) \
            -> Tuple[AStarSearchState, str, bool]:
        """
        Apply an action to a state and return the next state and feedback.
        """
        feedback = ""
        result_state = None
        done = False
        tactics = [action.tactic for action in actions]
        try:
            unit = self.server.load_sorry("\n".join(tactics + ["sorry"]))
            next_goal_state = unit[0].goal_state
            result_state = AStarSearchState(
                goal_state=next_goal_state,
                generator_score=action.generator_score,
                parent=state,
                parent_goal_id=goal_id
            )
            done = True
        except TacticFailure as t:
            feedback = str(t)
        except ServerError as e:
            feedback = f"Server Error: {e}"

        action.update_result_state(result_state, feedback)
        return result_state, feedback, done
    

class AStarSearchAgent():
    """
    A search agent that uses A* search algorithm to find a solution.
    """
    model: DojoModel
    env: PantographEnvironment
    heuristic: Optional[callable]
    cost: Optional[callable]
    guidance: Optional[callable]

    def __init__(self, model: DojoModel, env: PantographEnvironment, heuristic=None, cost=None, guidance=None):
        assert env.server.is_automatic()
        self.model = model
        self.env = env
        self.heuristic = heuristic if heuristic else self.default_heuristic
        self.cost = cost if cost else self.default_cost
        self.guidance = guidance if guidance else self.default_guidance
    
    def default_guidance(self, state: AStarSearchState) -> List[float]:
        """
        Return a list of priorities determining which goal should be searched
        first. This will not be called on states with one or zero goals.
        """
        priorities = [0.0] * len(state.goal_state.goals)
        return priorities
    
    def default_cost(self, current: AStarSearchState, neighbor: AStarSearchState) -> float:
        """
        Cost function for A* search.
        """
        return 1.0

    def default_heuristic(self, state: AStarSearchState) -> float:
        """
        Heuristic function for A* search.
        """
        return state.generator_score
    
    def get_successors(self, state: AStarSearchState, came_from: Dict[AStarSearchState, AStarSearchAction]) -> Tuple[List[AStarSearchAction], List[AStarSearchState]]:
        """
        Get the successors of the current state.
        """
        actions = self.model.generate_actions(state)
        print(actions)
        compiled_actions = []
        successors = []
        for action in actions:
            next_state, feedback, done = self.env.step(state, state.next_goal_id, action, self.reconstruct_path(came_from=came_from, current=state))
            if done:
                compiled_actions.append(action)
                successors.append(next_state)
        return compiled_actions, successors
    
    def reconstruct_path(self, came_from: Dict[AStarSearchState, AStarSearchAction], current: AStarSearchState) -> List[AStarSearchAction]:
        """
        Reconstruct the path from the initial state to the current state.
        """
        path = []
        while current in came_from:
            action = came_from[current]
            path.append(action)
            current = action.applied_state
        path.reverse()
        return path

    def search(self,
               initial_state: AStarSearchState,
               max_steps: int = 100,
               verbose: bool = False) -> Tuple[List[AStarSearchAction], bool, int, str]:
        """
        Executes proof search on this state
        """

        if initial_state.is_terminal:
            return [], True
    
        # Priority queue storing tuples of (f_score, g_score, current_node)
        queue = []
        heapq.heappush(queue, (self.heuristic(initial_state), 0, initial_state))
        came_from: Dict[AStarSearchState, AStarSearchAction] = {}
        g_score: Dict[AStarSearchState, float] = {initial_state: 0}
        step = 0

        while len(queue) > 0 and step < max_steps:
            if verbose:
                print(f"Step {step}: len(queue)={len(queue)}")
            step += 1
            _, g_current, current = heapq.heappop(queue)

            actions, successors = self.get_successors(current, came_from)
            if verbose:
                print(f"Current state: {current}")
                for successor in successors:
                    print(f"Successor: {successor}")

            for action, successor in zip(actions, successors):
                tentative_g = g_current + self.cost(current, successor)
                if successor not in g_score or tentative_g < g_score[successor]:
                    came_from[successor] = action
                    g_score[successor] = tentative_g
                    f_neighbor = tentative_g + self.heuristic(successor)
                    heapq.heappush(queue, (f_neighbor, tentative_g, successor))
                if successor.is_terminal:
                    return self.reconstruct_path(came_from, successor), True, step, "Proof found."
        
        if len(queue) == 0:
            return [], False, step, "No more states to explore."
        if step >= max_steps:
            return [], False, step, "Max steps reached."


if __name__ == '__main__':
    model = DojoModel()
    server = Server(project_path="./")
    env = PantographEnvironment(server)
    lean_sketch = """
    theorem mathd_algebra_478
      (b h v : ℝ)
      (h₀ : 0 < b ∧ 0 < h ∧ 0 < v)
      (h₁ : v = 1 / 3 * (b * h))
      (h₂ : b = 30)
      (h₃ : h = 13 / 2) :
      v = 65 := by sorry
    """
    unit, = server.load_sorry(lean_sketch)
    goal_state = unit.goal_state
    print(f"Initial state: {goal_state}")
    initial_state = AStarSearchState(
        goal_state=goal_state
    )
    search_agent = AStarSearchAgent(model, env)
    actions, solved, _, _ = search_agent.search(initial_state, max_steps=20, verbose=False)
    if solved:
        print("Proof found!")
        for action in actions:
            print(action.to_code())
    else:
        print("No proof found.")
