
{-
  In Agda können wir mit "A : Set" ausdrücken, dass "A" ein Typ ist.
  ( "{-", "-}" und "--" können für Kommentare verwendet werden)
-}

id : (A : Set) -> A -> A

{-
  Funktionsausdrücke wie "x ↦ x" werden in Agda so geschrieben "λ x -> x".
  Definitionale Gleichheit ":≡" wird als "=" geschrieben.
-}

id A = λ x -> x

{-
  Aufgabe 1: Definieren Komposition.
  Als Symbol kann "∘" verwendet werden, was man in Emacs' Agda modus durch
  Eingabe von "\circ" bekommt.
-}

-- ...

{-
  Wir schauen nun einen Typen an, den wir noch in der Vorlesung sehen werden.
-}

data Bool : Set where    -- "Bool" ist ein neuer Datentyp
  true : Bool            -- mit Konstruktoren "true" und "false"
  false : Bool

{-
  Funktionen auf Datentypen können in Agda durch "Pattern-Matching" definiert
  werden:
-}

not : Bool -> Bool
not true = false          -- sollte man lesen als "not(true):≡false"
not false = true

{-
  Hier ist eine gute Gelegenheit Normalisierung auszuprobieren -
  in Emacs' Agda-mode geht das mit C-c C-n.
  Man kann einen Ausrduck eingeben, wie z.B. "not (not false)"
  und Agda berechnet die Normalform des Ausdrucks (im Fall der
  induktiven Datentypen die wir hier verwerden, sollte das immer
  ein Ausdruck sein, der nur Konstruktoren verwendet).
  "not false" ist eine Funktionsanwendung - in Agda sind diese
  einfach hintereinanderschreiben, ohne die in der Mathematik
  üblichen Klammern.
-}

{-
  Aufgabe 2: Schreibe eine Funktion "and" mit zwei Argumenten,
  die das mathematische "und" implementiert.
-}

-- ...

{-
  Konstruktoren in Datentypen können auch Argumente haben,
  wie die Nachfolgeroperation in der folgenden Definition der
  natürlichen Zahlen.
-}

data Nat : Set where
  O : Nat                -- Null ist eine natürliche Zahl
  S : Nat -> Nat         -- Für jede Natürliche Zahl "n" gibt es einen Nachfolger
                         -- "S(n)"

{-
  Damit lassen sich alle natürlichen Zahlen ausdrücken.
-}

null = O
eins = S O
drei = S (S eins)

{-
  Wir definieren nun eine Verdopplungsfunktion auf "Nat"
  durch Pattern-Matching:
-}

d : Nat -> Nat           -- d x = 2·x
d O     = O              -- 2·0 = 0
d (S n) = S (S (d n))    -- 2·(n+1) = 2+2·n

{-
  Aufgabe 3:
  Definiere eine Funktion "even : Nat -> Bool", deren Wert bei "n:Nat"
  genau dann "true" ist, wenn "n" eine gerade natürliche Zahl ist.

even : Nat -> Bool
even = ?
-}


{-
  Aufgabe 4:
  Schreibe eine Funktion "=? : Nat -> Nat -> Bool"
  die genau dann "true" is, wenn die beiden Argumente
  gleich große natürliche Zahlen sind.

=? : Nat -> Nat -> Bool
=? = {!!}
-}

{-
  Wir definieren nun die Addition auf den natürlich Zahlen.
-}

plus : Nat -> Nat -> Nat
plus O = id Nat
plus (S n) = λ x → S (plus n x)

_+_ : Nat -> Nat -> Nat
O + k = k
S n + k = S (n + k)

{-
  Um den Quellcode zu verschönern kann man auch
  "\bN" tippen - was zu "ℕ" werden sollte.
  Außerdem kann man statt "->" auch "\to" verwenden.
  Weiter kann man mit "{}" anstelle von runden Klammern
  Argumente markieren, die man nicht angeben will - Agda
  wird dann versuchen die Argumente zu bestimmen.
-}







{-
  ↓↓↓ Lösungen der Aufgaben ↓↓↓
-}













{-
-- 1
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

-- 2
_and_ : Bool -> Bool -> Bool
true and true = true
true and false = false
false and true = false
false and false = false

-- 3
even : Nat -> Bool
even O = true
even (S n) = not (even n)

-- 4
=? : Nat -> Nat -> Bool
=? O O = true
=? O (S n) = false
=? (S k) O = false
=? (S k) (S n) = =? k n
-}
