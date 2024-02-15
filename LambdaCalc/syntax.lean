import Mathlib

--Syntax
inductive ty : Type
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty

inductive tm : Type
  | tm_var : String -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : String -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm

notation "<{" e:99 "}>" => e
notation S:50 " -> " T:50 => ty.Ty_Arrow S T
notation "λ" x " : " t ", " y => tm.tm_abs x t y
notation " Bool " => ty.Ty_Bool
notation "if " x:99 " then " y:99 " else " z:99 => tm.tm_if x y z
notation " true " => tm.tm_true
notation " false " => tm.tm_false
infixl:99 " ∘ " => tm.tm_app
