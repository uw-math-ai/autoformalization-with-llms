from transformers import AutoTokenizer, AutoModelForSeq2SeqLM

tokenizer = AutoTokenizer.from_pretrained("kaiyuy/leandojo-lean4-tacgen-byt5-small")
model = AutoModelForSeq2SeqLM.from_pretrained("kaiyuy/leandojo-lean4-tacgen-byt5-small")

state = "R : Type u_1\ninst✝ : CommRing R\na b c d : R\nhyp : c = d * a + b\nhyp' : b = a * d\n⊢ d * a + a * d = 2 * a * d"
tokenized_state = tokenizer(state, return_tensors="pt")

tactic_ids = model.generate(tokenized_state.input_ids, max_length=1024)
tactic = tokenizer.decode(tactic_ids[0], skip_special_tokens=True)
print(tactic, end="\n\n")

tactic_candidates = model.generate(
    tokenized_state.input_ids,
    max_length=1024,
    num_beams=4,
    length_penalty=0.0,
    do_sample=False,
    num_return_sequences=4,
    early_stopping=False,
    output_scores=True,
    return_dict_in_generate=True
)

for i, seq in enumerate(tactic_candidates.sequences):
    tactic = tokenizer.decode(seq, skip_special_tokens=True)
    seq_score = tactic_candidates.sequences_scores[i]
    print(tactic + f": {seq_score}", end="\n")