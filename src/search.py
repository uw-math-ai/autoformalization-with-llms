import heapq
from typing import Any, Callable, Dict, List, Optional, Tuple
import unittest

# TODO: Implement the heuristics functions based on the interface of NeuralProofState
def heuristic(neural_proof_state, generator_score):
    """
    Heuristic function for A* search.

    Parameters:
        neural_proof_state: The current state.
        generator_score: The score assigned by the generator.

    Returns:
        The estimated cost from the current node to the goal.
    """
    return 0


# TODO: Implement the get_neighbors function based on the interface of NeuralProofState and the generator
# TODO: If feasible, this function should be implemented with multiple threads to speed up the search
def get_neighbors(neural_proof_state):
    """
    Returns the neighbors of the current state and their scores assigned by the generator.

    Parameters:
        neural_proof_state: The current state.

    Returns:
        A tuple containing a list of neighbor nodes and a list of scores assigned by the generator.
    """
    return [], []


# TODO: Implement the cost function based on the interface of NeuralProofState
def cost(neural_proof_state, neighbor):
    """
    Returns the cost to move from the current state to a neighbor.

    Parameters:
        neural_proof_state: The current state.
        neighbor: The neighbor node.

    Returns:
        The cost to move from the current state to the neighbor.
    """
    return 1


def is_done(state: Any) -> bool:
    """
    Determines if the state is done.

    Parameters:
        state: The state to check.

    Returns:
        True if the state is done, False otherwise.
    """
    if state == 'D':
        return True
    else:
        return False


def print_current(current: Any) -> None:
    """
    Prints the current state.

    Parameters:
        current: The current state.
    """
    print(f'Start exploring state: {current}')


def astar_search(
    start: Any,
    heuristic: Callable[[Any, float], float],
    get_neighbors: Callable[[Any], Tuple[List[Any], List[float]]],
    cost: Callable[[Any, Any], float],
    max_iters: int = 100,
    verbose: bool = False
) -> Optional[List[Any]]:
    """
    Performs A* search from start to goal.

    Parameters:
        start: The starting state.
        heuristic: A function estimating the cost from a node to the goal given the score assigned by the generator. 
        get_neighbors: A function that returns a list of neighbor nodes with their scores assigned by the generator for a given node.
        cost: A function returning the cost to move from one node to a neighbor

    Returns:
        A list representing the path from start to goal if one exists, otherwise None.
    """
    if is_done(start):
        return [start]
    
    # Priority queue storing tuples of (f_score, g_score, current_node)
    queue = []
    heapq.heappush(queue, (heuristic(start, -1), 0, start))

    came_from: Dict[Any, Any] = {} 
    g_score: Dict[Any, float] = {start: 0}

    while len(queue) > 0 and max_iters > 0:
        _, g_current, current = heapq.heappop(queue)
        if verbose:
            print_current(current)

        neighbors, scores = get_neighbors(current)

        for neighbor, score in zip(neighbors, scores):
            tentative_g = g_current + cost(current, neighbor)
            if neighbor not in g_score or tentative_g < g_score[neighbor]:
                came_from[neighbor] = current
                g_score[neighbor] = tentative_g
                f_neighbor = tentative_g + heuristic(neighbor, score)
                heapq.heappush(queue, (f_neighbor, tentative_g, neighbor))
            if is_done(neighbor):
                return reconstruct_path(came_from, neighbor)
        
        max_iters -= 1

    return None  # No path found

def reconstruct_path(came_from: Dict[Any, Any], current: Any) -> List[Any]:
    """
    Reconstructs the path from start to goal using the came_from mapping.

    Parameters:
        came_from: A dictionary mapping each node to its predecessor.
        current: The goal node from which to start the reconstruction.

    Returns:
        A list of nodes representing the path from start to goal.
    """
    path = [current]
    while current in came_from:
        current = came_from[current]
        path.append(current)
    path.reverse()
    return path


class TestAStarSearch(unittest.TestCase):
    def setUp(self):
        self.graph = {
            'A': (['B', 'C'], [-0.8, -0.2]),
            'B': (['D', 'C'], [-0.5, -0.5]),
            'C': (['D'], [-1]),
            'D': ([], []),
            'E': (['E'], [-1])
        }
        self.get_neighbors = lambda node: self.graph.get(node, ([], []))
        self.heuristic = lambda node, float: float
        self.cost = lambda a, b: 1

    def test_path_found(self):
        # Test finding a path from 'A' to 'D'
        path = astar_search('A', self.heuristic, self.get_neighbors, self.cost)
        self.assertIn(path, [['A', 'B', 'D']])

    def test_start_equals_goal(self):
        # Test when start and goal are the same.
        path = astar_search('D', self.heuristic, self.get_neighbors, self.cost)
        self.assertEqual(path, ['D'])

    def test_no_path(self):
        # Test when no path exists (e.g., from 'E' to 'D')
        path = astar_search('E', self.heuristic, self.get_neighbors, self.cost)
        self.assertIsNone(path)


if __name__ == '__main__':
    unittest.main()

