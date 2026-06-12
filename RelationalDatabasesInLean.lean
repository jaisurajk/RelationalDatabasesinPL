/-!
# Relational Databases in Lean

This file is a small, dependency-free companion to the project report.
It models tables as lists of records and implements a few relational
algebra operations: selection, projection, Cartesian product, and joins.
-/

structure Product where
  isbn : Nat
  title : String
  price : Float
deriving Repr

structure ProductComment where
  isbn : Nat
  comment : String
deriving Repr

structure Customer where
  customerId : Nat
  name : String
deriving Repr

structure Order where
  orderId : Nat
  customerId : Nat
  isbn : Nat
  quantity : Nat
deriving Repr

def products : List Product :=
  [ { isbn := 123894523, title := "Databases in Lean", price := 22.22 }
  , { isbn := 534432123, title := "History of AI", price := 80.20 }
  , { isbn := 991122333, title := "Query Plans and Proofs", price := 45.00 }
  ]

def comments : List ProductComment :=
  [ { isbn := 123894523, comment := "Awesome!" }
  , { isbn := 123894523, comment := "Do not buy, overhyped." }
  , { isbn := 534432123, comment := "Only covers September 2018, avoid." }
  ]

def customers : List Customer :=
  [ { customerId := 1, name := "Ada" }
  , { customerId := 2, name := "Grace" }
  ]

def orders : List Order :=
  [ { orderId := 1001, customerId := 1, isbn := 123894523, quantity := 2 }
  , { orderId := 1002, customerId := 2, isbn := 534432123, quantity := 1 }
  , { orderId := 1003, customerId := 1, isbn := 991122333, quantity := 1 }
  ]

namespace List

/-- Cartesian product of two lists. -/
def outer {α β : Type _} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | [] => []
  | x :: xs' => (ys.map fun y => (x, y)) ++ xs'.outer ys

end List

/-- Relational selection: keep rows satisfying a Boolean predicate. -/
def select {α : Type _} (p : α → Bool) (rows : List α) : List α :=
  rows.filter p

/-- Relational projection: map each row to the selected output fields. -/
def project {α β : Type _} (f : α → β) (rows : List α) : List β :=
  rows.map f

/--
An inner join over two tables represented as lists.

The predicate decides which row pairs match, and the projection decides
what the output row should contain.
-/
def innerJoin {α β γ : Type _}
    (matchRows : α → β → Bool)
    (combine : α → β → γ)
    (xs : List α)
    (ys : List β) : List γ :=
  xs.outer ys
    |>.filter (fun pair => matchRows pair.1 pair.2)
    |>.map (fun pair => combine pair.1 pair.2)

def productTitles : List String :=
  project (fun p : Product => p.title) products

#eval productTitles

def productsUnder50 : List String :=
  products
    |> select (fun p => p.price < 50.0)
    |> project (fun p => p.title)

#eval productsUnder50

declare_syntax_cat leanq_clause (behavior := both)
syntax &"project " term : leanq_clause
syntax &"select " term : leanq_clause
syntax term:max " in " term : leanq_clause

syntax "from " leanq_clause,* : term

macro_rules
  | `(from $x:term in $lst, select $cond, project $val) =>
    `($lst |> select (fun $x => $cond) |> project (fun $x => $val))

def productsUnder50' : List String :=
  from p in products,
    select p.price < 50.0,
    project p.title

#eval productsUnder50'

def productCommentPairs : List (String × String) :=
  innerJoin
    (fun p c => p.isbn == c.isbn)
    (fun p c => (p.title, c.comment))
    products
    comments

#eval productCommentPairs

def customerOrderPairs : List (String × Nat × Nat) :=
  innerJoin
    (fun c o => c.customerId == o.customerId)
    (fun c o => (c.name, o.isbn, o.quantity))
    customers
    orders

#eval customerOrderPairs

theorem outer_nil_left {α β : Type _} (ys : List β) :
    ([] : List α).outer ys = [] := by
  rfl

theorem outer_nil_right {α β : Type _} (xs : List α) :
    xs.outer ([] : List β) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [List.outer, ih]

theorem select_true {α : Type _} (rows : List α) :
    select (fun _ => true) rows = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [select]

theorem select_false {α : Type _} (rows : List α) :
    select (fun _ => false) rows = [] := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [select]

theorem innerJoin_empty_left {α β γ : Type _}
    (matchRows : α → β → Bool)
    (combine : α → β → γ)
    (ys : List β) :
    innerJoin matchRows combine [] ys = [] := by
  rfl

theorem innerJoin_empty_right {α β γ : Type _}
    (matchRows : α → β → Bool)
    (combine : α → β → γ)
    (xs : List α) :
    innerJoin matchRows combine xs [] = [] := by
  simp [innerJoin, outer_nil_right]

theorem project_empty {α β : Type _} (f : α → β) :
    project f [] = [] := by
  rfl

theorem concreteCommentJoin :
    productCommentPairs =
      [ ("Databases in Lean", "Awesome!")
      , ("Databases in Lean", "Do not buy, overhyped.")
      , ("History of AI", "Only covers September 2018, avoid.")
      ] := by
  native_decide
