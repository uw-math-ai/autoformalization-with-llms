import sys

import os
import dotenv
import litellm
from litellm import completion
import json
sys.path.append(os.path.join(os.path.dirname(__file__), '../src'))

from predictnextstep import predict_next_step
from neuralproofstate import NeuralProofState

dotenv.load_dotenv()

os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_API_KEY")
os.environ["OPENAI_API_BASE"] = os.getenv("OPENAI_API_BASE", "https://api.openai.com/v1")

def load_lean_phrasebook():
    phrasebook = [
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Observe that A holds because of reason r",
    "Lean equivalent": "have h:A := by r",
    "Notes": "Can omit h, in which case the result is called `this` by default\nIf the reason r is a one-liner, \"observe h:A\" can work"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Observe that X is equal to Y by definition",
    "Lean equivalent": "have : X = Y := by rfl",
    "Notes": "or \"observe : X = Y\""
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We claim that A holds. \u00A0...",
    "Lean equivalent": "have h:A := by\n\u00A0 \u00A0<proof of A>",
    "Notes": None
  },
  {
    "Goal": "A",
    "(Selected) hypotheses": "h: A",
    "Step (in mathematical english)": "The claim follows",
    "Lean equivalent": "assumption",
    "Notes": "Can also use `exact h`"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "This follows by definition",
    "Lean equivalent": "rfl",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "This follows by reason r",
    "Lean equivalent": "exact r",
    "Notes": "Can try exact? to find if an exact solution already exists"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "By A, it suffices to show that ... ",
    "Lean equivalent": "apply A",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: A",
    "Step (in mathematical english)": "Using h, we may reduce to",
    "Lean equivalent": "simp [h]",
    "Notes": "can combine multiple simplfiications using simp [h1, h2, ...]\ncan use `simp only [hypotheses]` for a more targeted simplification\ncan try simp? to suggest tools to use"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: A",
    "Step (in mathematical english)": "We can rewrite our goal using A as ...",
    "Lean equivalent": "rw [h]",
    "Notes": "also have `nth_rewrite n [h]` for more precise rewriting\ncan combine multiple rewrites using rw [h,h',...]\nIf one wants to apply h in reverse, use rw [<- h]\nA rewrite that turns a goal into an existing assumption can close the proof using rwa [h]\nIf one needs to use associativity before rewriting, use assoc_rw"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We can rewrite our goal using A (which is true for reason r) as ...",
    "Lean equivalent": "rw [(show A by r)]",
    "Notes": "Can also use (by r: A) instead of (show A by r)"
  },
  {
    "Goal": "A",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Applying reason r to A, we conclude B",
    "Lean equivalent": "have h:B := r A",
    "Notes": None
  },
  {
    "Goal": "A ∧ B",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "First we prove A. \u00A0...\u00A0\nNow we prove B. ...",
    "Lean equivalent": "constructor\n. <proof of A>\n<proof of B>",
    "Notes": None
  },
  {
    "Goal": "A ∧ B ∧ C ∧ D",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We now prove each of A, B, C, D in turn.",
    "Lean equivalent": "refine ⟨ ?_, ?_, ?_, ?_ ⟩",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: A ∧ B",
    "Step (in mathematical english)": "By hypothesis, we have A and B",
    "Lean equivalent": "rcases \u00A0h with \\langle hA, hB \\rangle",
    "Notes": "can also use h.1 and h.2\nan intro followed by rcases can be merged into an rintro. \u00A0\nA rcases item \u00A0that is used immediately for rw can be replaced with an rfl"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: A ∧ B ∧ C ∧ D",
    "Step (in mathematical english)": "By hypothesis, we have A, B, C, D",
    "Lean equivalent": "obtain ⟨ hA, hB, hC, hD ⟩ := h",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "From h, we obtain A and B",
    "Lean equivalent": None,
    "Notes": "Also works for more complex expressions than simple conjunctions"
  },
  {
    "Goal": "A \u229c B",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "First we prove A implies B. ...\nNow we prove B implies A",
    "Lean equivalent": "constructor\n. <proof of A implies B>\n<proof of B implies A>",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We will obtain a contradiction",
    "Lean equivalent": "exfalso",
    "Notes": None
  },
  {
    "Goal": "A ∨ B",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It will suffice to prove A",
    "Lean equivalent": "left",
    "Notes": "can also use Or.inl"
  },
  {
    "Goal": "A ∨ B",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It will suffice to prove B",
    "Lean equivalent": "right",
    "Notes": "can also use Or.inr"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: A ∨ B",
    "Step (in mathematical english)": "We divide into cases. \u00A0\nFirst, suppose that A holds. \u00A0...\nNow, suppose that B holds ...",
    "Lean equivalent": "rcases h with ha | hb",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We divide into cases depending on the natural number n\nFirst, suppose that n=0. \u00A0...\nNow, suppose that n=m+1 for some m ...",
    "Lean equivalent": "rcases n with _ | m",
    "Notes": "Also works for other inductive types than the natural numbers, e.g., finite sets"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We divide into cases. \u00A0\nFirst, suppose that A is true. \u00A0...\nNow, suppose that A is false ...",
    "Lean equivalent": "\nby_cases h:A\n. <proof assuming A>\n<proof assuming not-A>",
    "Notes": "can also use\nrcases em A with ha | hna\n. <proof assuming A>\n<proof assuming not-A>"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We divide into cases.\nFirst, suppose that n=0. ...\nNext, suppose that n=1. ...\nFinally, suppose that n is of the form n+2...",
    "Lean equivalent": "match n with\n| 0 => ...\n| 1 => ...\n| n+2 => ...\n",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: A, nh: not-A",
    "Step (in mathematical english)": "But this is absurd.",
    "Lean equivalent": "absurd h nh",
    "Notes": "One can save a line or two sometimes by deriving A or not-A directly, e.g., using the `(show A by r)` syntax"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "A, not-A",
    "Step (in mathematical english)": "This gives the required contradiction.",
    "Lean equivalent": "contradiction",
    "Notes": None
  },
  {
    "Goal": "A",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Suppose for contradiction that A fails",
    "Lean equivalent": "by_contra nh",
    "Notes": None
  },
  {
    "Goal": "not-A",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Suppose for contradiction that A holds",
    "Lean equivalent": "intro ha",
    "Notes": None
  },
  {
    "Goal": "A",
    "(Selected) hypotheses": "h: B",
    "Step (in mathematical english)": "Taking contrapositives, it suffices to show that not-A implies not-B.",
    "Lean equivalent": "contrapose! h",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We compute\nx = y (by reason r)\n= z (by reason s)\n= w (by reason t)",
    "Lean equivalent": "calc x = y \u00A0:= by r\n\u00A0 _ = z := by s\n\u00A0 _ = w := by t",
    "Notes": "Calc can also handle chained inequalities like ≤ and <. \u00A0gcongr is a useful tactic to justify intermediate steps in such cases"
  },
  {
    "Goal": "A implies B",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Thus, suppose that A holds.",
    "Lean equivalent": "intro ha",
    "Notes": "For complex hypotheses it can be convenient to use rintro instead\nCan omit ha, in which case the hypothesis of A is placed in `this`"
  },
  {
    "Goal": "∀ x ∈ X, A",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Now let x be an element of X.",
    "Lean equivalent": "intro x, hx",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "ha: a ∈ X\nh: ∀ x ∈ X: A(x)",
    "Step (in mathematical english)": "Since a is in X, A(a) holds",
    "Lean equivalent": "have haa := h a ha",
    "Notes": "If one wants to use A(a) directly one can just use `h a ha` anywhere one would have otherwise used haa\nCan also use `specialize h a ha`, but this replaces h with `h a ha`."
  },
  {
    "Goal": "∃ x, A",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We will take x to equal a",
    "Lean equivalent": "use a",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: ∃ x A",
    "Step (in mathematical english)": "By hypothesis, there exists x obeying A",
    "Lean equivalent": "rcases h with \\langle x, hxa \\rangle",
    "Notes": None
  },
  {
    "Goal": "A",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We need to show A'",
    "Lean equivalent": "show A'",
    "Notes": "If there are multiple goals, show finds the goal that matches A' and moves it to the front of the goal queue"
  },
  {
    "Goal": "A",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "By definition, we may rewrite the hypothesis A as A'",
    "Lean equivalent": "change A' at A",
    "Notes": "can siimilarly use \"change X\" to change the goal to a definitionally equivalent X"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h:A \u00A0f: A ⇒ B",
    "Step (in mathematical english)": "By f, we may replace A by B",
    "Lean equivalent": "replace h := f h",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: A",
    "Step (in mathematical english)": "We may replace A with B by reason r",
    "Lean equivalent": "replace h : B := by r",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: A",
    "Step (in mathematical english)": "The hypothesis A is no longer needed and can be discarded.",
    "Lean equivalent": "clear h",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "ha: A\nhb: B",
    "Step (in mathematical english)": "The only hypotheses we will use in the sequel are A and B",
    "Lean equivalent": "clear_except hA hB",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We simplify this as",
    "Lean equivalent": "simp",
    "Notes": "If one simplifies to one of the assumptions, we can use `simpa` instead of `simp` and `assumption`"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h : A",
    "Step (in mathematical english)": "We can simplify the hypothesis A as",
    "Lean equivalent": "simp at h",
    "Notes": "Can be combined with [hypotheses], `simp only`, etc. \u00A0Can also use wildcard *"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "By definition, this can be rewritten as",
    "Lean equivalent": "dsimp",
    "Notes": "Is a more restrictive version of simp, only uses definitional equalities."
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "But this follows from the laws of algebra in a ring",
    "Lean equivalent": "ring",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Since we are in a field, we can simplify this to",
    "Lean equivalent": "field_simp [hypotheses]",
    "Notes": "field_simp is good for clearing denominators; often followed by ring. \u00A0Hypotheses of denominators being non-zero are located automatically, or introduced as additional goals"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h : A",
    "Step (in mathematical english)": "Since we are in a field, we can simplify A to",
    "Lean equivalent": "field_simp [hypotheses] at h",
    "Notes": "\u00A0"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "But this follows from the laws of linear inequalities",
    "Lean equivalent": "linarith",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "But this follows (by logical tautology)",
    "Lean equivalent": "tauto",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h : A",
    "Step (in mathematical english)": "Since we are in a field, we can simplify A to",
    "Lean equivalent": "field_simp [hypotheses] at h",
    "Notes": "\u00A0"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "But this follows from the laws of linear inequalities",
    "Lean equivalent": "linarith",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "But this follows (by logical tautology)",
    "Lean equivalent": "tauto",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Which can be numerically verified",
    "Lean equivalent": "norm_num",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "negating all the quantifiers, we reduce to showing",
    "Lean equivalent": "push_neg",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "One is now tempted to try...",
    "Lean equivalent": "apply?",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "To conclude, one could try",
    "Lean equivalent": "exact?",
    "Notes": None
  },
  {
    "Goal": "f=g",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It suffices to show that f(x)=g(x) for every x",
    "Lean equivalent": "ext x",
    "Notes": None
  },
  {
    "Goal": "S = T",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It suffices to show that x ∈ S iff x ∈ T",
    "Lean equivalent": "ext x",
    "Notes": None
  },
  {
    "Goal": "sum_{x in X} f(x) = sum_{x in X} g(x)",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It suffices to show that for all x in X, that f(x) = g(x)",
    "Lean equivalent": "Finset.sum_congr rfl",
    "Notes": "If g is ranging over another set Y, can replace rfl here with a proof that X=Y"
  },
  {
    "Goal": "f(x)=f(y)",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It will suffice to show that x=y",
    "Lean equivalent": "congr",
    "Notes": "sometimes congr! works better. \u00A0Sometimes congr breaks things down too much, and one has to use congr 1, congr 2, etc. instead or the more precise congrm"
  },
  {
    "Goal": "x+y ≤ x'+y'",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It suffices to show that x ≤ x' and y ≤ y'",
    "Lean equivalent": "gcongr",
    "Notes": "Works well with calc. \u00A0If sums or products are involved, may need to use \"gcongr with i hi\" etc. in order to access the bound variables"
  },
  {
    "Goal": "X ⊂ Y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Let x ∈ X. \u00A0We need to show that x ∈ Y",
    "Lean equivalent": "intro x hx",
    "Notes": None
  },
  {
    "Goal": "x in X ∪ Y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "x is in X or x is in Y",
    "Lean equivalent": "rintro xX | xY",
    "Notes": None
  },
  {
    "Goal": "x in X ∩ Y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "x is in X and x is in Y",
    "Lean equivalent": "rintro \\langle xX, xY \\rangle",
    "Notes": None
  },
  {
    "Goal": "X = Y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It suffices to show X ⊂ Y and Y ⊂ X",
    "Lean equivalent": "apply Subset.antisymm",
    "Notes": None
  },
  {
    "Goal": "x = y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It suffices to show x ≤ y and y ≤ x",
    "Lean equivalent": "apply le_antisymm",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We induct on n.\nFirst we establish the base case n=0. ...\nNow suppose inductively that the claim holds for n. \u00A0..",
    "Lean equivalent": "induction' n with n ih\n. <proof of base case>\n<proof of inductive case>",
    "Notes": None
  },
  {
    "Goal": "X=Y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We rewrite our goal as Y=X",
    "Lean equivalent": "symm",
    "Notes": None
  },
  {
    "Goal": "A",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We claim it suffices to show B. ...\nNow we show B. ...",
    "Lean equivalent": "suffices B by\n\u00A0 <proof of A given B>\n<proof of B>",
    "Notes": "If B is very close in form to A, convert can work (and if B is definitionally equal to A, change can work)"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We replace X by Y, which is possible thanks to r",
    "Lean equivalent": "rw [(show X=Y by r)]",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: X = Y",
    "Step (in mathematical english)": "Applying f to both sides, we conclude f(X)=f(Y)",
    "Lean equivalent": "apply_fun f at h",
    "Notes": "Can also use `replace h := congr_arg f h` \u00A0or `replace h := by congrm (f $h)`.\nSimilarly can use congrm (1 + $h) to add 1 to both sides, etc.\ngcongr can be used in situations where one is proving inequalities rather than equalities."
  },
  {
    "Goal": "something involving (if A then x else y)",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "First suppose that A is true.\nNow suppose that A is false.",
    "Lean equivalent": "split\n. <proof if A is true>\n<proof if A is false>",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Expanding out all the definitions, our goal is to establish",
    "Lean equivalent": "unfold",
    "Notes": "Can also \"unfold at h\" to expand out h. Can use dunfold if one only wants to expand using definitional equalities"
  },
  {
    "Goal": "x>0 or x >= 0",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "This positivity is clear from the hypotheses",
    "Lean equivalent": "positivity",
    "Notes": None
  },
  {
    "Goal": "f(x:\\N) = f(x:\\R)",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "This expression is the same whether we think of x as a natural number or a real",
    "Lean equivalent": "norm_cast",
    "Notes": None
  },
  {
    "Goal": "c + b + a = b + a + d",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We move all the a terms to the left, and the b terms to the right",
    "Lean equivalent": "move_add [<- a b]",
    "Notes": "move_mul is similar, but for products"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Let X denote the quantity Y",
    "Lean equivalent": "let X := Y",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We will abbreviate the expression Y as X",
    "Lean equivalent": "set X := Y",
    "Notes": "The difference between this and let is that it actively seeks out all occurrences of Y and replaces them with X\nCan use set X := Y with h if one wants to use h : X = Y as a hypothesis\nCan also use generalize : Y = X (or generalize h : Y = X) to make X a new variable rather than definitionally equal to Y"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We prove the latter goal first",
    "Lean equivalent": "swap",
    "Notes": "Also `swap n`, `rotate`, and `rotate n` for similar goal permuting maneuvers"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We claim A. \u00A0(proof of A). \u00A0We now continue with the rest of the proof.",
    "Lean equivalent": "have h:A",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Later we will prove A. \u00A0Assuming this claim for the moment .... . \u00A0Now, we prove A.",
    "Lean equivalent": "suffices h : A from\n\u00A0<proof assuming h>\n<proof of A>",
    "Notes": "can also use `have h : A; swap`"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Suppose P is true. \u00A0(some arguments) we now conclude Q is true. \u00A0In summary, P implies Q.",
    "Lean equivalent": "have hPQ (hP: P) : ?Q := by\n\u00A0 -- (some arguments reaching a conclusion hQ:Q)\u00A0\n\u00A0 exact hQ",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We now perform the following arguments. \u00A0(some arguments). \u00A0In summary, we have established P.",
    "Lean equivalent": "have hP: ?P := by\n\u00A0 -- (some arguments reaching a conclusion hP:P)\n\u00A0 exact hP",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Let n be a natural number. \u00A0(some arguments) We now conclude that P(n) is true. \u00A0\nIn summary, P(n) is true for all natural numbers .",
    "Lean equivalent": "have hP (n : \\Nat) : ?P := by\n\u00A0 -- (some arguments reaching a conclusion hP: P n)\n\u00A0 exact hP",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Without loss of generality we may assume P.",
    "Lean equivalent": "wlog h : P\n. <proof assuming not-P, and that the goal was provable assuming P>\n<proof assuming P>",
    "Notes": "See also \"wlog h : P generalizing ...\" to generalize selected variables"
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": "h: X' ≤ Y'",
    "Step (in mathematical english)": "It suffices to show that X=X' and Y=Y'",
    "Lean equivalent": "convert h using 1",
    "Notes": "Works for many more general relations than ≤ here; can also work with other depths of conversion than 1"
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": "h: X ≤ Z",
    "Step (in mathematical english)": "It suffices to show that Z ≤ Y",
    "Lean equivalent": "apply h.trans",
    "Notes": "can also use `apply le_trans h _`"
  },
  {
    "Goal": "X<Y",
    "(Selected) hypotheses": "h: X ≤ Z",
    "Step (in mathematical english)": "It suffices to show that Z < Y",
    "Lean equivalent": "apply h.trans_lt",
    "Notes": None
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": "h: Z ≤ Y",
    "Step (in mathematical english)": "It suffices to show that X ≤ Y",
    "Lean equivalent": "apply le_trans _ h",
    "Notes": None
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": "h: X = Z",
    "Step (in mathematical english)": "It suffices to show that Z ≤ Y",
    "Lean equivalent": "rw [h]",
    "Notes": None
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": "h: Z = Y",
    "Step (in mathematical english)": "It suffices to show that X ≤ Z",
    "Lean equivalent": "rw [<- h]",
    "Notes": None
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": "h: X' ≤ Y'",
    "Step (in mathematical english)": "It suffices to show that X ≤ X' and Y' ≤ Y",
    "Lean equivalent": "apply le_trans _ (le_trans h _)",
    "Notes": None
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "Suppose for contradiction that Y < X",
    "Lean equivalent": "by_contra h; simp at h",
    "Notes": None
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It suffices to show that f(X) ≤ f(Y) (because f is an order isomorphism)",
    "Lean equivalent": "apply_fun f",
    "Notes": "See https://leanprover-community.github.io/mathlib_docs/tactics.html#apply_fun for several variants of this"
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It suffices to show that X + Z ≤ Y + Z",
    "Lean equivalent": "rw [<- add_le_add_right]",
    "Notes": "many variants, e.g., add_le_add_left, sub_le_sub_right , etc."
  },
  {
    "Goal": "X ≤ Y",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "It suffices to show that X Z ≤ Y Z (and that Z>0)",
    "Lean equivalent": "apply mul_le_mul_right",
    "Notes": None
  },
  {
    "Goal": "A\nB\nC",
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We establish all these goals by the same argument:",
    "Lean equivalent": "all_goals { <list of tactics> }",
    "Notes": "Can enclose <list of tactics> inside (try...) in case some of the goals cannot be accomplished this way the braces {} can be dropped if there is only one tactic, and you do not expect to always close the argument"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We conjecture that A holds",
    "Lean equivalent": "theorem A_conj : A := by sorry",
    "Notes": "Can use `have` instead of `theorem` inside a proof environment"
  },
  {
    "Goal": None,
    "(Selected) hypotheses": None,
    "Step (in mathematical english)": "We may rewrite our goal using the identity (x+y)(x-y)=x^2-y^2 as",
    "Lean equivalent": "rw [show ∀ x :ℝ, ∀ y : ℝ, (x+y)*(x-y) = x*x-y*y by intros; ring]",
    "Notes": None
  },
  {
    "Goal": "∀ᶠ x in f, Q x",
    "(Selected) hypotheses": "h: ∀ᶠ x in f, P x\nh': ∀ᶠ x in f, P' x",
    "Step (in mathematical english)": "It suffices to show Q x for x obeying P x and P' x",
    "Lean equivalent": "filter_upwards [h, h']",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: Nonempty A",
    "Step (in mathematical english)": "We arbitrarily select an element x from the nonempty set A",
    "Lean equivalent": "obtain ⟨ x ⟩ := h",
    "Notes": None
  },
  {
    "Goal": None,
    "(Selected) hypotheses": "h: Nonempty A",
    "Step (in mathematical english)": "We use a canonical choice function to select an element x from the nonempty set A",
    "Lean equivalent": "x = h.some",
    "Notes": "Can also use x = h.arbitrary or x = Classical.choice h"
  }
]
    return json.dumps(phrasebook)


def get_natural_language_proof(state: str) -> str:
    lean_phrasebook = load_lean_phrasebook()
    prompt = f"""The following is a reference of Lean phrases:
    {lean_phrasebook}

    The following is a theorem written in Lean 4 syntax:

    {state}

    Provide a **step-by-step explanation in natural language** for how to prove this theorem mathematically. 
    Use clear reasoning but do not use Lean code or Lean tactics. Provide lean-style reasoning.
    The goal is to understand the strategy for proving the theorem before formalizing it.
    """
    try:
        response = completion(
            model="o3-mini",
            messages=[{"role": "user", "content": prompt}],
            max_tokens=5000,
            temperature=0.7,
        )
        return response.choices[0].message["content"].strip()
    except Exception as e:
        print(f"Error while generating natural language proof: {e}")
        return ""
    

if __name__ == "__main__":    
#     state = """mathd_algebra_141
#   (a b : ℝ)
#   (h₁ : (a * b)=180)
#   (h₂ : 2 * (a + b)=54) :
#   (a^2 + b^2) = 369 := by"""
    
#     prev_tactics = """have h₃ : a + b = 27 := by linarith,
#     have h₄ : a^2 + b^2 = (a + b)^2 - 2 * a * b := by ring"""
    
    state = """mathd_algebra_141
  (x p : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < p ∧ p < 15)
  (h₁ : p ≤ x ∧ x ≤ 15)
  (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
  15 ≤ f x := by"""
    
    prev_tactics = None

    informal_info = get_natural_language_proof(state)
    print(informal_info)
    
    nps = NeuralProofState(state=state, prev_tactics=prev_tactics, informal_info=informal_info)

    tactics = predict_next_step(nps, num_tactics=3, temperature=1.5)

    print("Predicted next steps:")
    for tactic in tactics:
        #print(f" ({tactic['log_probability']}) {tactic['tactic']}")
        print(f"{tactic['tactic']}")
