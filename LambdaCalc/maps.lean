import LambdaCalc.semantics
import LambdaCalc.syntax
import Mathlib

------ Total and Partial Maps

def total_map (A : Type) := String → A

def empty_map {A : Type} (v : A) : total_map A :=
  fun _ => v

def t_update {A : Type} (m : String → A) (x : String) (v : A) : String → A :=
  fun x' => if x = x' then v else m x'

notation x " !-> " v " ; " m => t_update m x v

def partial_map (α : Type) := total_map (Option α)

def empty {α : Type} : partial_map α :=
  empty_map none

def update {A : Type} (m : partial_map A) (x : String) (v : A) : partial_map A :=
  x !-> some v ; m

notation x " |-> " v " ; " m => update m x v

---- We say a map f is included in f' if all the entries in f appear in f'
def includedin {A : Type} (m m' : partial_map A) :=
  ∀ x v, m x = some v → m' x = some v

---- Map update preserves inclusion:
-- lemma includedin_update : ∀ (T : Type) (m m' : partial_map T) (x : String) (v : T),
-- includedin m m' → includedin (x |-> v; m) (x |-> v; m') := by
-- unfold includedin
-- intros T m m' x v H
-- intros x1 x2 HT
-- by_cases h : x1 = x
-- · rw [h] at HT
--   rw [h]
