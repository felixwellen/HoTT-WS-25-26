{- Der folgende "import" erlaubt uns "𝒰" statt "Set" zu schreiben -}

open import Agda.Primitive
           using ()
           renaming (Set to 𝒰)  -- \McU für 𝒰

{-
  Dies ist eine verkürzte, veränderte und ergänzte Version von intro.agda,
  die als Grundlage für die Lösung der Aufgaben auf Blatt 2 dienen kann.
  Außerdem kann man hier auch grob den Stand der Vorlesung in Agda sehen.
-}

id : (A : 𝒰) → A → A    -- \to für →
id A = λ x → x            -- \lambda für λ

_∘_ : {A B C : 𝒰} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

data Bool : 𝒰 where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data ℕ : 𝒰 where    -- \bN für ℕ
  O : ℕ
  S : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
O + k = k
S n + k = S (n + k)


data 𝟙 : 𝒰 where
  ∗ : 𝟙

data ∅ : 𝒰 where   -- \emptyset für ∅

-- Das Koprodukt aus der VL
data _⊔_ (A B : 𝒰) : 𝒰 where    -- \sqcup für ⊔
  ι₁ : A → A ⊔ B
  ι₂ : B → A ⊔ B

data _≈_ {A : 𝒰} : A → A → 𝒰 where   -- \~~ oder \approx für ≈
  refl : {x : A} → x ≈ x                 -- Abhängigkeit von Termen wird durch "A → A → 𝒰" realisiert
                                         -- "{...}" lassen Agda das Argument ("x" und "A") berechnen.

≈𝟙 : (x : 𝟙) → x ≈ ∗
≈𝟙 ∗ = refl

≈⊔ : (x : Bool) → (x ≈ true) ⊔ (x ≈ false)
≈⊔ true = ι₁ refl
≈⊔ false = ι₂ refl

isProp∅ : (x y : ∅) → x ≈ y
isProp∅ ()

_⁻¹ : {A : 𝒰} {x y : A} → x ≈ y → y ≈ x   -- \^-\^1 für ⁻¹
refl ⁻¹ = refl

_∙_ : {A : 𝒰} {x y z : A} → x ≈ y → y ≈ z → x ≈ z
refl ∙ refl = refl
infixr 21 _∙_                                         -- Priorität für _∙_ höher als ≈
                                                      -- (festlegen auf rechtsassoziativität)

assoc : {A : 𝒰} {x y z u : A} (γ : x ≈ y) (η : y ≈ z) (ι : z ≈ u) → γ ∙ (η ∙ ι) ≈ (γ ∙ η) ∙ ι
assoc refl refl refl = refl

ap : {A B : 𝒰} {x y : A} (f : A → B) → x ≈ y → f x ≈ f y
ap f refl = refl

infix 21 _+_ -- priorität von + sollte höher als die der Gleichheit sein
n+0≈n : (n : ℕ) → n + O ≈ n
n+0≈n O = refl
n+0≈n (S n) = ap S (n+0≈n n)

n+k≈k+n : (n k : ℕ) → n + k ≈ k + n
n+k≈k+n O k = (n+0≈n k) ⁻¹
n+k≈k+n (S n) k = ap S (n+k≈k+n n k) ∙ lemma k n
  where
  lemma : (n k : ℕ) → S(n + k) ≈ n + S k
  lemma O k = refl
  lemma (S n) k = ap S (lemma n k)

refl-linksneutral : {A : 𝒰} {x y : A} (p : x ≈ y) → refl ∙ p ≈ p
refl-linksneutral refl = refl

refl-rechtsneutral : {A : 𝒰} {x y : A} (p : x ≈ y) → p ∙ refl ≈ p
refl-rechtsneutral refl = refl

∙-linksinvers : {A : 𝒰} {x y : A} (p : x ≈ y) → p ⁻¹ ∙ p ≈ refl
∙-linksinvers refl = refl

-- transport
tr : {A : 𝒰} {x y : A} (B : A → 𝒰) (p : x ≈ y) → B(x) → B(y)
tr B (refl {x = x}) = id (B(x))                                  -- s.u.
{-
  wenn man doch mal ein Argument angeben möchte, das man mit {...}
  für implizit erklärt hat, kann man das z.B. mit {x = x} machen.
  Das linke "x" ist hier der Name aus der definition von "refl".
-}

infixr 21 _∘_

tr-functorial : {A : 𝒰} {x y z : A} (B : A → 𝒰) (p : x ≈ y) (q : y ≈ z)
                → tr B q ∘ tr B p ≈ tr B (p ∙ q)                             -- Zeilenumbrüche sind ok
tr-functorial B refl refl = refl

infix 22 _⁻¹   -- Inversion sollte höhere Priorität als ∙ haben
-- dieses Beispiel funktioniert nur, weil wir hier ∙ entsprechend definiert haben
tr-l≈ : {A : 𝒰} (y₀ : A) {u v : A} (p : u ≈ v) (q : u ≈ y₀)
        → tr (λ x → x ≈ y₀) p q ≈ p ⁻¹ ∙ q
tr-l≈ y₀ refl refl = refl

tr-r≈ : {A : 𝒰} (x₀ : A) {u v : A} (p : u ≈ v) (q : x₀ ≈ u)
        → tr (λ y → x₀ ≈ y) p q ≈ (q ∙ p)
tr-r≈ _ refl refl = refl

data Σ (A : 𝒰) (B : A → 𝒰) : 𝒰 where
  _,_ : (x : A) (y : B x) → Σ A B

infixr 2 _,_

π₁ : {A : 𝒰} {B : A → 𝒰} → Σ A B → A
π₁ (x , y) = x

π₂ : {A : 𝒰} {B : A → 𝒰} → (x : Σ A B) → B (π₁ x)
π₂ (x , y) = y

_×_ : (A B : 𝒰) → 𝒰
A × B = Σ A (λ _ → B)

ex-ℕ : (x : ℕ) → (x ≈ O) ⊔ (Σ ℕ (λ y → x ≈ S y))
ex-ℕ O = ι₁ refl
ex-ℕ (S x) = ι₂ (x , refl)

isContr : (A : 𝒰) → 𝒰
isContr A = Σ A (λ (x : A) → (y : A) → y ≈ x)

Σ-≈ : {A : 𝒰} {B : A → 𝒰} {x y : A} {u : B x} {v : B y}
      → Σ (x ≈ y) (λ p → tr B p u ≈ v) → (x , u) ≈ (y , v)
Σ-≈ (refl , refl) = refl

{-
  Der Beweis von Lemma 1.6.9 ist tatsächlich einfacher als in der VL gezeigt
  - ich hatte eine mögliche Gleichheitsinduktion übersehen...
-}
lemma-Σ-≈ : (A : 𝒰) (x : A) → isContr (Σ A (λ y → y ≈ x))
lemma-Σ-≈ A x = (x , refl) , helper
  where
    helper : (z : Σ A (λ y → y ≈ x)) → z ≈ (x , refl)
    helper (y , refl) = refl -- In der VL stand hier p statt refl und wir haben
                             -- inetwa das gemacht: Σ-≈ (p , (tr-l≈ _ p p ∙ ∙-linksinvers p))

isProp : (A : 𝒰) → 𝒰
isProp A = (x y : A) → x ≈ y

is_Type : (n : ℕ) (A : 𝒰) → 𝒰   -- Wir sind hier um 2 versetzt zur Vorlesung
is O Type A = isContr A
is (S n) Type A = (x y : A) → is n Type (x ≈ y)

apd : {A : 𝒰} {B : A → 𝒰} {x y : A} (f : (z : A) → B z) → (p : x ≈ y) → tr B p (f x) ≈ f y
apd f refl = refl

∙-cancel-l : {A : 𝒰} {x y z : A} (r : x ≈ y) (p q : y ≈ z) → r ∙ p ≈ r ∙ q → p ≈ q
∙-cancel-l refl p q refl∙p≈refl∙q = refl-linksneutral p ⁻¹ ∙ refl∙p≈refl∙q ∙ refl-linksneutral q

isProp≈ : (A : 𝒰) (isPropA : isProp A) → (x y : A) → isProp (x ≈ y)
isProp≈ A isPropA x y p q = ∙-cancel-l (isPropA x x) p q helper
  where helper : (isPropA x x) ∙ p ≈ (isPropA x x) ∙ q
        helper = tr-r≈ x p (isPropA x x) ⁻¹
                 ∙ (apd (isPropA x) p
                 ∙ apd (isPropA x) q ⁻¹)
                 ∙ tr-r≈ x q (isPropA x x)

isProp→is1Type : {A : 𝒰} → isProp A → is (S O) Type A
isProp→is1Type isPropA x y = isPropA x y , λ p → isProp≈ _ isPropA x y p _

isnType→isSnType : {A : 𝒰} (n : ℕ) → is n Type A → is (S n) Type A
isnType→isSnType O     h x y = let isPropA = λ x y → (π₂ h x ∙ π₂ h y ⁻¹)
                               in isPropA x y , λ p → isProp≈ _ isPropA _ _ _ _
isnType→isSnType (S n) h x y = isnType→isSnType n (h x y)

_~_ : {A B : 𝒰} (f g : A → B) → 𝒰
f ~ g = (x : _) → f x ≈ g x

_∙~_ : {A B : 𝒰} {f g h : A → B} → f ~ g → g ~ h → f ~ h
H ∙~ K = λ x → H x ∙ K x

refl~ : {A B : 𝒰} {f : A → B} → f ~ f
refl~ = λ x → refl

_⁻¹~ : {A B : 𝒰} {f g : A → B} → f ~ g → g ~ f
H ⁻¹~ = λ x → H x ⁻¹

ap~ : {A B C : 𝒰} {f g : A → B} (h : B → C) → f ~ g → h ∘ f ~ h ∘ g
ap~ h H = λ x → ap h (H x)

precomp~ : {A B C : 𝒰} {f g : A → B} (h : C → A) → f ~ g → f ∘ h ~ g ∘ h
precomp~ h H = λ x → H (h x)

qInv : {A B : 𝒰} (f : A → B) → 𝒰
qInv {A} {B} f = Σ (B → A) (λ g → (g ∘ f ~ id A) × (f ∘ g ~ id B))

isEquiv : {A B : 𝒰} (f : A → B) → 𝒰
isEquiv {A} {B} f = (Σ (B → A) (λ g → g ∘ f ~ id A)) × (Σ (B → A) (λ h → (f ∘ h ~ id B)))

idEquiv : (A : 𝒰) → isEquiv (id A)
idEquiv A = ((id A) , refl~) , ((id A) , refl~)

qInv→isEquiv : {A B : 𝒰} (f : A → B) → qInv f → isEquiv f
qInv→isEquiv f (g , (g∘f~id , f∘g~id)) = (g , g∘f~id) , (g , f∘g~id)

equiv-linv-rinv :
  {A B : 𝒰} (f : A → B) (l : B → A)
  → isEquiv f → l ∘ f ~ id _ → f ∘ l ~ id _
equiv-linv-rinv {A} {B} f l ((lf , p) , (rf , q)) l∘f~id =
  λ (x : B) →  ap (f ∘ l) (q x ⁻¹)
             ∙ ap f (l∘f~id (rf x))
             ∙ q x

isEquiv→qInv : {A B : 𝒰} (f : A → B) → isEquiv f → qInv f
isEquiv→qInv f isEquivf@((g , p) , (h , q)) = g , (p , (equiv-linv-rinv f g isEquivf p))

logicalEquiv→Equiv : {A B : 𝒰} → isProp A → isProp B → (f : A → B) → (g : B → A) → isEquiv f
logicalEquiv→Equiv isPropA isPropB f g =
  (g , (λ x → isPropA (g (f x)) x)) , (g , (λ x → isPropB (f (g x)) x))

_≃_ : (A B : 𝒰) → 𝒰    -- \simeq für "≃"
A ≃ B = Σ (A → B) (λ f → isEquiv f)


{-
  Wir führen nun sogenanntes "Equational reasoning" ein - d.h. wir wollen
  Gleichungsketten als    x₀ ≈⟨ p₀ ⟩ x₁ ≈⟨ p₁ ⟩ x₂ ... xₙ₋₁ ≈⟨ pₙ ⟩ xₙ ≈∎
  schreiben. Das können wir durch folgende Auswertungsreihenfolge realisieren:

      x₀ ≈⟨ p₀ ⟩ (x₁ ≈⟨ p₁ ⟩ (x₂ ... (xₙ₋₁ ≈⟨ pₙ ⟩ (xₙ ≈∎))...)

  Analoges definieren wir für "≃" und "~".
-}

infixr 4 _≈⟨_⟩_
_≈⟨_⟩_ : {A : 𝒰} {y : A} {z : A} (x : A) (p : x ≈ y) (q : y ≈ z) → x ≈ z  -- \< für ⟨, \> für ⟩
x ≈⟨ p ⟩ q = p ∙ q

infix 5 _≈∎
_≈∎ : {A : 𝒰} → (x : A) → x ≈ x
x ≈∎ = refl

infixr 4 _~⟨_⟩_
_~⟨_⟩_ : {A B : 𝒰} {g h : A → B} (f : A → B) (H : f ~ g) (K : g ~ h) → f ~ h  -- \< für ⟨, \> für ⟩
x ~⟨ H ⟩ K = H ∙~ K

infix 5 _~∎
_~∎ : {A B : 𝒰} → (f : A → B) → f ~ f
x ~∎ = λ x → refl

{- Komposition von Äquivalenzen können wir nicht einfach auch mit "∘" bezeichnen wie in der Vorlesung
   Stattdessen hängen wir einfach "≃" an...
   Außerdem zeigen wir in der Konstruktion beispielhaft die Verwendung der neuen Syntax.
-}
_∘≃_ : {A B C : 𝒰} → B ≃ C → A ≃ B → A ≃ C
(g , eg) ∘≃ (f , ef) = (g ∘ f) , ((f⁻¹ ∘ g⁻¹ ,
                                   λ x →
                                   ((f⁻¹ ∘ g⁻¹) ∘ g ∘ f) x ≈⟨ ap (π₁ fQ) (π₁ (π₂ gQ) (f x)) ⟩
                                   f⁻¹ (f x)               ≈⟨ π₁ (π₂ fQ) x ⟩
                                   x                       ≈∎  ) ,
                                   (f⁻¹ ∘ g⁻¹ ,
                                    (g ∘ f) ∘ f⁻¹ ∘ g⁻¹  ~⟨ precomp~ g⁻¹ (ap~ g (π₂ (π₂ fQ))) ⟩
                                    g ∘ g⁻¹              ~⟨ π₂ (π₂ gQ) ⟩
                                    id _                 ~∎))
  where
     gQ : qInv g
     gQ = isEquiv→qInv g eg
     g⁻¹ = π₁ gQ

     fQ : qInv f
     fQ = isEquiv→qInv f ef
     f⁻¹ = π₁ fQ


infixr 3 _≃⟨_⟩_
_≃⟨_⟩_ : {B C : 𝒰} (A : 𝒰) (f : A ≃ B) (g : B ≃ C) → A ≃ C  -- \< für ⟨, \> für ⟩
A ≃⟨ f ⟩ g = g ∘≃ f

infix 4 _≃∎
_≃∎ : (A : 𝒰) → A ≃ A
A ≃∎ = id A , idEquiv A



{-
     A
    f↓ ↘gf
     B─g→C
     hg↘ ↓h
         D

-}

6-for-2 : {A B C D : 𝒰} → (f : A → B) → (g : B → C) → (h : C → D)
          → isEquiv (g ∘ f) → isEquiv (h ∘ g)
          → isEquiv f × (isEquiv g × isEquiv h)
6-for-2 f g h isEgf isEhg = isEf , (isEg , isEh)
  where gfQ : qInv (g ∘ f)
        hgQ : qInv (h ∘ g)
        gfQ = isEquiv→qInv (g ∘ f) isEgf
        hgQ = isEquiv→qInv (h ∘ g) isEhg
        ⟨gf⟩⁻¹ = π₁ gfQ
        ⟨hg⟩⁻¹ = π₁ hgQ

        isEg : isEquiv g
        isEg = (⟨hg⟩⁻¹ ∘ h , π₁ (π₂ hgQ)) , (f ∘ ⟨gf⟩⁻¹) , π₂ (π₂ gfQ)
        gQ = isEquiv→qInv g isEg
        g⁻¹ = π₁ gQ

        isEf : isEquiv f
        isEf = ((⟨gf⟩⁻¹ ∘ g) , π₁ (π₂ gfQ)) ,
               (⟨gf⟩⁻¹ ∘ g ,
                 f ∘ ⟨gf⟩⁻¹ ∘ g             ~⟨ precomp~ (f ∘ ⟨gf⟩⁻¹ ∘ g) (π₁ (π₂ gQ) ⁻¹~) ⟩
                 g⁻¹ ∘ (g ∘ f ∘ ⟨gf⟩⁻¹) ∘ g ~⟨ precomp~ g (ap~ g⁻¹ (π₂ (π₂ gfQ))) ⟩
                 g⁻¹ ∘ g                    ~⟨ π₁ (π₂ gQ) ⟩
                 id _ ~∎)

        isEh : isEquiv h
        isEh = (g ∘ ⟨hg⟩⁻¹ ,
                 (g ∘ ⟨hg⟩⁻¹) ∘ h               ~⟨ ap~ ((g ∘ ⟨hg⟩⁻¹) ∘ h) (π₂ (π₂ gQ) ⁻¹~)  ⟩
                 g ∘ (⟨hg⟩⁻¹ ∘ h ∘ g) ∘ g⁻¹     ~⟨ precomp~ g⁻¹ (ap~ g (π₁ (π₂ hgQ))) ⟩
                 g ∘ g⁻¹                        ~⟨ π₂ (π₂ gQ) ⟩
                 id _ ~∎) ,
               (g ∘ ⟨hg⟩⁻¹ , π₂ (π₂ hgQ))


{-
  Funktionsextensionalität
-}

happly : {A : 𝒰} {B : A → 𝒰} (f g : (x : A) → B x) → f ≈ g → (x : A) → f x ≈ g x
happly f g p = λ x → ap (λ h → h x) p

postulate
  happlyIsEquiv : {A : 𝒰} {B : A → 𝒰} {f g : (x : A) → B x} → isEquiv (happly f g)

funext : {A B : 𝒰} {f g : A → B} → f ~ g → f ≈ g
funext {f = f} {g = g} = π₁ (isEquiv→qInv (happly f g) happlyIsEquiv)

isPropIsContr : (A : 𝒰) → isProp (isContr A)
isPropIsContr A (x , p) (y , q) = Σ-≈ (q x , {!q x!})
