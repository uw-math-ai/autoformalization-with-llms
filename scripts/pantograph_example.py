# the Python code to perform autoformalization

from pantograph.server import Server

if __name__ == '__main__':
    server = Server(project_path="./")

    # prove a theorem
    state0 = server.goal_start("forall (p q: Prop), Or p q -> Or q p")
    print("state0: ", state0, "\n")
    state1 = server.goal_tactic(state0, goal_id=0, tactic="intro p q h")
    print("Used tactic: `intro p q h`")
    print("state1:\n", state1, "\n")
    state2 = server.goal_tactic(state1, goal_id=0, tactic="rcases h with hp | hq")
    print("Used tactic: `rcases h with hp | hq`")
    print("state2:\n", state2, "\n")
    state3 = server.goal_tactic(state2, goal_id=0, tactic="right")
    print("Used tactic: `right`")
    print("state3:\n", state3, "\n")
    state4 = server.goal_tactic(state3, goal_id=0, tactic="exact hp")
    print("Used tactic: `exact hp`")
    print("state4:\n", state4, "\n")
    state5 = server.goal_tactic(state4, goal_id=0, tactic="left")
    print("Used tactic: `left` on goal 1")
    print("state5:\n", state5, "\n")
    state6 = server.goal_tactic(state5, goal_id=0, tactic="exact hq")
    print("Used tactic: `exact hq`")
    print("state6:\n", state6, "\n")
    assert state6.is_solved