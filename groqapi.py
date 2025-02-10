import os
import re

from groq import Groq

client = Groq(
    api_key=os.environ.get("GROQ_API_KEY"),
)

header = """import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Basic

open Function
variable {α : Type _} (r s t : Set α)

"""

theorems = [
    """theorem thm1 (a b c : Nat) : a + b = c → a ≤ c := by {}""",
    """theorem thm2 (x y : ℝ) : x < y → 0 < y - x := by {}""",
    """theorem thm3 (n : Nat) : n ≥ 0 := by {}""",
    """theorem thm4 (x y z : ℝ) : x ≤ y → y ≤ z → x ≤ z := by {}""",
    """theorem thm5 (m n : Nat) (h : m.coprime n) : m.gcd n = 1 := by {}""",
    """theorem thm6: r ⊆ s → s ⊆ t → r ⊆ t := by {}""",
    """theorem thm7 (f : ℕ → ℕ) : Monotone f → ∀ n, f n ≤ f (n + 1) := by {}""",
    """theorem thm8 (c : ℝ) : Injective fun x => x + c := by {}""",
    """theorem thm9 (A B : Set ℕ) : A ⊆ B → ∀ n, n ∈ A → n ∈ B := by {}""",
    """theorem thm10 (injg : Injective g) (injf : Injective f) : Injective fun x => g (f x) := by {}""",
]

def format_response(theorem, response):
    response = response.strip()
    
    if response.startswith("theorem"):
        response = re.sub(r"theorem.*?:\s*by", "", response, flags=re.DOTALL).strip()
    
    tactics = "\n".join([f"  {line.strip()}" for line in response.splitlines()])
    
    formatted_output = f"{theorem.replace(':= by {}', ':= by')}\n{tactics}"
    
    return formatted_output

responses = []
for theorem in theorems:

    full_content = f"{header}\n{theorem}"
    
    chat_completion = client.chat.completions.create(
        messages=[
            {
                "role": "user",
                "content": f"Given the Lean code:\n\n{full_content}\n\nProvide the entire proof using Lean tactics. Give only the Lean tactic steps and no other information in your response. Do not include 'by' at the start of your response, as it is already included in the theorem header."
            }
        ],
        model="llama-3.3-70b-versatile",
    )
    
    responses.append(chat_completion.choices[0].message.content)

for i, response in enumerate(responses):
    formatted_response = format_response(theorems[i], response)
    print(f"{formatted_response}\n")