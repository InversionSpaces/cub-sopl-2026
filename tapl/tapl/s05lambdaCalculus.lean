/-
5.2.2 : Church Numeral Other Succ

5.2.3 : Church Numeral Mult, No Plus?

5.2.4 : Church Numeral pow

5.2.5 : Subtraction using pred

5.2.6 : Steps to calculate pred

5.2.7 : Equality for Church Numerals

5.2.8 : List implementation in a Lambda Calculus
· Nil, Cons definition
· IsNil, Head definition
· tail definition

5.2.9 : Replace if with test in the definition of g (factorial Church numerals)

5.2.10 : Convert Nat to Church Numeral

5.2.11 : List concatenation operator using Fix

5.3.3 : |FV t| ≤ size t

5.3.6 : Evaluation for Lambda Terms
· full β-reduction
· normal-order
· lazy evaluation

5.3.7 : Extend Wrong (5.3.16) to λNB
⇑ Probably non-trivial

5.3.8 : Big-Step style for λNB
-/

inductive LTerm
| Var (x : Nat)
| Abs (t : LTerm)
| App (t1 : LTerm) (t2 : LTerm)

def lid := LTerm.Abs (.Var 0)

def tru :=
  LTerm.Abs
    (.Abs
      (.Var 0))

def fls :=
  LTerm.Abs
    (.Abs
      (.Var 1))

def test :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.App
            (.Var 0)
            (.Var 1))
          (.Var 2))))

def land :=
  LTerm.Abs
    (.Abs
      (.App
        (.App
          (.Var 0)
          (.Var 1))
        fls))

def lor :=
  LTerm.Abs
    (.Abs
      (.App
        (.App
          (.Var 0)
          tru)
        (.Var 1)))

def lnot :=
  LTerm.Abs
    (.App
      (.App
        (.Var 0)
        tru)
      fls)

def lpair :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.App
            (.Var 2)
            (.Var 0))
          (.Var 1))))

def fst :=
  LTerm.Abs
    (.App
      (.Var 0)
      tru)

def snd :=
  LTerm.Abs
    (.App
      (.Var 0)
      fls)

def c0 :=
  LTerm.Abs
    (.Abs
      (.Var 1))

def scc :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.Var 1)
          (.App
            (.App
              (.Var 0)
              (.Var 1))
            (.Var 2)))))

--5.2.2
def my_scc :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.App
          (.App
            (.Var 0)
            (.Var 1))
          (.App
            (.Var 1)
            (.Var 2)))))

def plus :=
  LTerm.Abs
    (.Abs
      (.Abs
        (.Abs
          (.App
            (.App
              (.Var 0)
              (.Var 2))
            (.App
              (.App
                (.Var 1)
                (.Var 2))
              (.Var 3))))))

def times :=
  LTerm.Abs
    (.Abs
      (.App
        (.App
          (.Var 0)
          (.App
            plus
            (.Var 1)))
        c0))

--5.2.3
def my_times :=
  LTerm.Abs
    (.Abs
      (.App
        (.Var 0)
        (.Var 1)))
