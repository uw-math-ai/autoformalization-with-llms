from pantograph.server import Server

def parse_tactics():
    tactics = [ # Example tactic, same as autoformalize.py
        "intro p q h",
        "rcases h with hp | hq",
        "right",
        "exact hp",
        "left",
        "exact hq"
    ]
    return tactics

if __name__ == '__main__':
    server = Server(project_path="./")
    state = server.goal_start("forall (p q: Prop), Or p q -> Or q p")

    encountered_states = [state]
    i = 0

    tactics = parse_tactics()

    while not state.is_solved:
        prev_state = state
        print(f"state{i}: {state} \n")
        tactic = tactics.pop(0)

        try:
            new_state = server.goal_tactic(state, goal_id=0, tactic=tactic)
            i+= 1
            if not new_state in encountered_states: # check if we possibly regressed to a previous goal state
                state = new_state
                encountered_states.append(state)

        except Exception as e:
            tactics.append(tactic)
            print(e)
            encountered_states.remove(state)
            state = prev_state
