from abc import ABC, abstractmethod
import heapq
from typing import List, Tuple, Optional, Dict
import os

from transformers import AutoModelForSeq2SeqLM, AutoTokenizer
from transformers.generation.utils import GenerateBeamEncoderDecoderOutput
import dotenv
from litellm import completion
from pantograph.expr import Tactic, GoalState
from pantograph.server import Server, TacticFailure, ServerError


class AStarSearchState():
    """
    An implementation of the SearchState interface.
    Represents a state in the A* search algorithm.
    """

    state: GoalState
    priorities: list[float]
    generator_score: float
    # parent: Optional['AStarSearchState']
    # parent_goal_id: Optional[int]
    
    def __init__(
            self,
            goal_state,
            priorities=None,
            generator_score=None,
            # parent=None,
            # parent_goal_id=None
        ):
        self.state = goal_state
        if priorities is not None:
            self.priorities = priorities
        elif goal_state is None:
            self.priorities = []
        else:
            self.priorities = [0.0] * len(goal_state.goals)
        self.generator_score = generator_score if generator_score is not None else 0.0
        # self.parent = parent
        # self.parent_goal_id = parent_goal_id

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
        return self.state is None or self.state.is_solved
    
    def __str__(self):
        return f"AStarSearchState(goal_state={self.state}, generator_score={self.generator_score}, priorities={self.priorities})"
    
    def __lt__(self, other):
        return self.generator_score < other.generator_score
    
    def __eq__(self, other):
        return isinstance(other, AStarSearchState) and self.state == other.state
    
    def __hash__(self):
        return hash(self.state.state_id) if self.state is not None else hash(None)


class AStarSearchAction():
    """
    An implementation of the SearchAction interface.
    Represents an action in the A* search algorithm.
    """

    applied_state: AStarSearchState
    goal_id: int
    tactic: Tactic
    generator_score: float
    # result_state: Optional[AStarSearchState]
    # feedback: Optional[str]

    def __init__(
            self,
            applied_state,
            goal_id,
            tactic,
            generator_score=None,
            # result_state=None,
            # feedback=None
        ):
        self.applied_state = applied_state
        self.goal_id = goal_id
        self.tactic = tactic
        self.generator_score = generator_score if generator_score is not None else 0.0
        # self.result_state = result_state
        # self.feedback = feedback

    # def update_result_state(self, result_state, feedback=None):
    #     self.result_state = result_state
    #     self.feedback = feedback

    def __str__(self):
        return f"AStarSearchAction(tactic={str(self.tactic)}, generator_score={self.generator_score})"
    
    def to_code(self):
        """
        Convert the action to a string representation.
        """
        return str(self.tactic)
      
    def __eq__(self, other):
        return isinstance(other, AStarSearchAction) and \
            self.tactic == other.tactic and \
            self.applied_state == other.applied_state and \
            self.goal_id == other.goal_id

class GenerationModel(ABC):
    """
    Interface for a generation model.
    """
    @abstractmethod
    def generate_actions(self,
            current_state: AStarSearchState,
            current_code: str,
            **generate_config
        ) -> List[AStarSearchAction]:
        """
        Generates a list of actions based on the current state.
        """
        pass

class DojoModel(GenerationModel):
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
        self.device = device if device else "cpu"
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
        goal = current_state.state.goals[current_state.next_goal_id]
        prompt = str(goal)
        
        return prompt

    def generate(self, prompt: str, **generate_config) -> GenerateBeamEncoderDecoderOutput:
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
        results = {}

        for i, seq in enumerate(outputs.sequences):
            tactic = self.tokenizer.decode(seq, skip_special_tokens=True)
            seq_score = -(outputs.sequences_scores[i].item())
            if tactic in results:
                results[tactic] = min(results[tactic], seq_score)
            else:
                results[tactic] = seq_score
        
        actions = []
        for tactic, seq_score in results.items():
            action = AStarSearchAction(current_state, current_state.next_goal_id, tactic, seq_score)
            actions.append(action)

        return actions

    def generate_actions(self, current_state: AStarSearchState, current_code: str, **generate_config) \
          -> List[AStarSearchAction]:
        prompt = self.format_prompt(current_state)
        raw_output = self.generate(prompt, **generate_config)
        actions =  self.format_output(current_state, raw_output)
        return actions
    
class LLMModel(GenerationModel):
    """
    A generation model that uses the LLM API
    """
    def __init__(self, **generate_config):
        """
        Initializes the wrapper by loading the model and tokenizer.
        """
        dotenv.load_dotenv()
        os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")
        self.generate_config = {
            "model": "gpt-4o-mini",
            "max_tokens": 100,
            "temperature": 1.0,
            "top_p": 0.9,
            "n": 10,
            "logprobs": True, 
        }
        if generate_config:
            self.generate_config.update(generate_config)

    def format_prompt(self, current_state: AStarSearchState, current_code: str) -> str:
        """
        Formats the prompt for the model based on the goal to solve.
        """
        goal = current_state.state.goals[current_state.next_goal_id]
        prompt = f"Given the Lean 4 proof state of a theorem: \n{goal}\n" + \
        f"Provide the next tactic to progress towards proving the theorem. " + \
        f"The previous code used to prove this theorem are as follows: \n{current_code}\n" + \
        f"Give only the next Lean tactic and no other information in your response."
      
        return prompt
    
    def generate(self, prompt: str, **generate_config):
        """
        Generates text based on the provided prompt.
        """
        params = {
            "messages": [{"role": "user", "content": prompt}]
        }
        params.update(self.generate_config)
        params.update(generate_config)

        try:
            response = completion(**params)
            return response
        except Exception as e:
            return []
        
    def format_output(self, current_state: AStarSearchState, response) -> List[AStarSearchAction]:
        """
        Formats the generated text into the desired output structure.
        """
        results = {}

        for choice in response.choices:
            tactic = choice.message["content"].strip()
            if choice.logprobs:
                sum_logprob = sum(token.logprob for token in choice.logprobs.content)
            else:
                sum_logprob = None
            
            if tactic in results and results[tactic] is not None and sum_logprob is not None:
                    results[tactic] = min(results[tactic], sum_logprob)
            else:
                results[tactic] = sum_logprob

        actions = []
        for tactic, sum_logprob in results.items():
            action = AStarSearchAction(current_state, current_state.next_goal_id, tactic, -sum_logprob)
            actions.append(action)

        return actions

    def generate_actions(self, current_state: AStarSearchState, current_code: str, **generate_config) \
          -> List[AStarSearchAction]:
        prompt = self.format_prompt(current_state, current_code)
        response = self.generate(prompt, **generate_config)
        actions = self.format_output(current_state, response)
        return actions

class PantographEnvironment():
    """
    An environment that uses Pantograph to apply actions to a state.
    """
    server: Server

    def __init__(self, server):
        self.server = server

    def step(
            self,
            current_state: AStarSearchState,
            current_code: str,
            goal_id: int, 
            action: AStarSearchAction,
        ) \
            -> Tuple[AStarSearchState, str, bool]:
        """
        Apply an action to a state and return the next state and feedback.
        """
        feedback = ""
        result_state = None
        done = False
        try:
            sketch = self.add_action_to_sketch(current_state, current_code, goal_id, action)
            unit = self.server.load_sorry(sketch)
            next_goal_state = unit[0].goal_state
            error_messages = [s for s in unit[0].messages if "error" in s]
            if len(error_messages) > 1:
                raise TacticFailure(' '.join(error_messages))
            elif len(error_messages) == 1 and "no goals to be solved" not in error_messages[0]:
                raise TacticFailure(error_messages[0])
            result_state = AStarSearchState(
                goal_state=next_goal_state,
                generator_score=action.generator_score,
                # parent=state,
                # parent_goal_id=goal_id
            )
            done = True
        except TacticFailure as t:
            feedback = str(t)
        except ServerError as e:
            feedback = f"Server Error: {e}"

        # action.update_result_state(result_state, feedback)
        return result_state, feedback, done
    
    # TODO: Need to apply tactic depending on the goal_id i.e. indentation and \mid
    def add_action_to_sketch(
            self,
            current_state: AStarSearchState,
            current_code: str,
            goal_id: int,
            action: AStarSearchAction
        ) -> str:
        """
        Add an action to the current code.
        """
        sketch = current_code + "\n  " + action.to_code() + "\n  sorry"
        return sketch

class AStarSearchAgent():
    """
    A search agent that uses A* search algorithm to find a solution.
    """
    model: GenerationModel
    env: PantographEnvironment
    heuristic: Optional[callable]
    cost: Optional[callable]
    guidance: Optional[callable]

    def __init__(
            self,
            model: GenerationModel,
            env: PantographEnvironment,
            heuristic=None,
            cost=None,
            guidance=None
        ):
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
        priorities = [0.0] * len(state.state.goals)
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
    
    def get_successors(self, current_state: AStarSearchState, current_code: str) \
            -> Tuple[List[AStarSearchAction], List[AStarSearchState]]:
        """
        Get the successors of the current state.
        """
        actions = self.model.generate_actions(current_state=current_state, current_code=current_code)
        compiled_actions = []
        successors = []
        for action in actions:
            next_state, feedback, done = self.env.step(
                current_state=current_state,
                current_code=current_code,
                goal_id=action.applied_state.next_goal_id,
                action=action
            )
            if done:
                compiled_actions.append(action)
                successors.append(next_state)
        return compiled_actions, successors
    
    def reconstruct_path(
            self,
            came_from: Dict[AStarSearchState, AStarSearchAction],
            current: AStarSearchState
        ) -> List[AStarSearchAction]:
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
    
    # TODO: Need to add tactic depending on the goal_id it is applied to i.e. indentation and \mid
    def get_current_code(
            self,
            initial_sketch: str,
            actions: List[AStarSearchAction]  
        ) -> str:
        """
        Get the current code from the initial sketch and actions applied.
        """
        current_code = "\n  ".join([initial_sketch] + [action.to_code() for action in actions])
        return current_code

    def search(self,
               lean_sketch: str,
               max_steps: int = 100,
               verbose: bool = False) -> Tuple[List[AStarSearchAction], bool, int, str]:
        """
        Executes proof search on this state
        """
        initial_sketch = lean_sketch.strip('\n ')
        unit = self.env.server.load_sorry(initial_sketch + " sorry")
        goal_state = unit[0].goal_state
        error_messages = [s for s in unit[0].messages if "error" in s]
        if len(error_messages) > 1:
            if verbose:
                print("Failed to create a goal state.")
            return [], False, 0, f"Failed to create a goal state: {" ".join(error_messages)}"
        elif len(error_messages) == 1 and "no goals to be solved" not in error_messages[0]:
            if verbose:
                print("Failed to create a goal state.")
            return [], False, 0, f"Failed to create a goal state: {error_messages[0]}"
        elif goal_state is None:
            if verbose:
                print("No goals to solve.")
            return [], False, 0, "No goals to solve."
        
        initial_state = AStarSearchState(
            goal_state=goal_state
        )
    
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

            current_actions = self.reconstruct_path(came_from, current)
            current_code = self.get_current_code(initial_sketch, current_actions)
            actions, successors = self.get_successors(current, current_code)
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
    model = LLMModel()
    server = Server(project_path="./", imports=['Mathlib.Data.Real.Cardinality', 'Mathlib.Data.Real.Basic'])
    env = PantographEnvironment(server)
    lean_sketch = """theorem mathd_algebra_44
  (s t : ℝ)
  (h₀ : s = 9 - 2 * t)
  (h₁ : t = 3 * s + 1) :
  s = 1 ∧ t = 4 := by"""
    search_agent = AStarSearchAgent(model, env)
    actions, solved, steps, feedback = search_agent.search(lean_sketch=lean_sketch, max_steps=20, verbose=False)
    if solved:
        print(f"Proof found in {steps} steps!")
        for action in actions:
            print(action.to_code())
    else:
        print(f"No proof found: {feedback}")
