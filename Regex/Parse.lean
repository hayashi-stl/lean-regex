import Regex.Defs

set_option linter.style.whitespace false
namespace Regex

declare_syntax_cat term'
scoped syntax:max str : term'
scoped syntax:max char : term'
scoped syntax:max num : term'
scoped syntax:max scientific : term'
scoped syntax:max ident : term'
scoped syntax:max name : term'
-- using a different currency symbol here for antiquoting regexes
scoped syntax:max "`‹" term:min "›" : term'

declare_syntax_cat regex
scoped syntax:max "⊥" : regex
scoped syntax:max "ε" : regex
scoped syntax:max str : regex
scoped syntax:max term':max : regex
scoped syntax:max "⟨" term:min "⟩" : regex
scoped syntax:70 regex:71 ppSpace regex:70 : regex
scoped syntax:55 regex:56 " | " regex:55 : regex
scoped syntax:max regex:max "*" : regex
scoped syntax:max "⊢" : regex
scoped syntax:max "⊣" : regex
scoped syntax:max "(" regex:min ")" : regex
scoped syntax:max "(" term':max " ← " regex:min ")" : regex
--scoped syntax:max "\\(" term:21 " <|> " regex:min ")" : regex
scoped syntax:max "\\⊥" term':max : regex
scoped syntax:max "\\ε" term':max : regex
scoped syntax:max "\\‹" term:min "›" term':max : regex

scoped syntax:max "[/" "/]" : term
scoped syntax:max (name := regex) "[/" regex "/]" : term
scoped syntax:max "[‹" term' "›]" : term

macro_rules
  | `([‹ $t:str ›]) => `($t)
  | `([‹ $t:char ›]) => `($t)
  | `([‹ $t:num ›]) => `($t)
  | `([‹ $t:scientific ›]) => `($t)
  | `([‹ $t:ident ›]) => `($t)
  | `([‹ $t:name ›]) => `($t)
  | `([‹ `‹ $t:term › ›]) => `($t)
  | `([//]) => `(empty)

open Lean PrettyPrinter Delaborator SubExpr

macro_rules
  | `([/ ⊥ /]) => `(bot)
  | `([/ ε /]) => `(empty)
  | `([/ /]) => `(empty)
  | `([/ $t:term' /]) => `(unit [‹ $t ›])
  | `([/ ⟨ $t:term ⟩ /]) => `($t)
  | `([/ $s:str /]) => `(string $s)
  | `([/ $t:regex $u:regex /]) => `(concat [/$t/] [/$u/])
  | `([/ $t:regex | $u:regex /]) => `(or [/$t/] [/$u/])
  | `([/ $t:regex * /]) => `(star [/$t/])
  | `([/ ⊢ /]) => `(start)
  | `([/ ⊣ /]) => `(end')
  | `([/ ( $t:regex ) /]) => `([/$t/])
  | `([/ ( $n:term' ← $t:regex ) /]) => `(capture [‹ $n ›] [/$t/])
  | `([/ \⊥ $n:term' /]) => `(backref [/⊥/] [‹ $n ›])
  | `([/ \ε $n:term' /]) => `(backref [//] [‹ $n ›])
  | `([/ \‹ $d:term › $n:term' /]) => `(backref $d [‹ $n ›])

/-- Turns a ```TSyntax `term``` into a ```TSyntax `regex``` by
extracting a wrapped regex -/
partial def unwrapRegex : TSyntax `term → DelabM (TSyntax `regex)
  | `([/ $r /]) => pure r
  | `([//]) => do unwrapRegex (← `([/ ε /]))
  | x => do unwrapRegex (← `([/ ⟨ $x ⟩ /]))

/-- Turns a ```TSyntax `term``` into a ```TSyntax `term'``` by
extracting a wrapped term' -/
partial def unwrapTerm' : TSyntax `term → DelabM (TSyntax `term')
  | `([‹ $r ›]) => pure r
  | _ => failure

/-- Turns a unit ```TSyntax `term``` into a ```TSyntax `regex``` -/
def termRegex : TSyntax `term → DelabM (TSyntax `regex)
  | `($t:str) => do unwrapRegex (← `([/ $(TSyntax.mk t) /]))
  | `($t:char) => do unwrapRegex (← `([/ $(TSyntax.mk t) /]))
  | `($t:num) => do unwrapRegex (← `([/ $(TSyntax.mk t) /]))
  | `($t:scientific) => do unwrapRegex (← `([/ $(TSyntax.mk t) /]))
  | `($t:ident) => do unwrapRegex (← `([/ $(TSyntax.mk t) /]))
  | `($t:name) => do unwrapRegex (← `([/ $(TSyntax.mk t) /]))
  | `($t:term) => do unwrapRegex (← `([/ `‹ $t › /]))

/-- Turns a unit ```TSyntax `term``` into a ```TSyntax `term'``` -/
def termTerm' : TSyntax `term → DelabM (TSyntax `term')
  | `($t:str) => do unwrapTerm' (← `([‹ $(TSyntax.mk t) ›]))
  | `($t:char) => do unwrapTerm' (← `([‹ $(TSyntax.mk t) ›]))
  | `($t:num) => do unwrapTerm' (← `([‹ $(TSyntax.mk t) ›]))
  | `($t:scientific) => do unwrapTerm' (← `([‹ $(TSyntax.mk t) ›]))
  | `($t:ident) => do unwrapTerm' (← `([‹ $(TSyntax.mk t) ›]))
  | `($t:name) => do unwrapTerm' (← `([‹ $(TSyntax.mk t) ›]))
  | `($t:term) => do unwrapTerm' (← `([‹ `‹ $t › ›]))

def unitRegex : Expr → DelabM (TSyntax `regex) | e => do termRegex (← delab e)

def exprTerm' : Expr → DelabM (TSyntax `term') | e => do termTerm' (← delab e)

def exprRegex : Expr → DelabM (TSyntax `regex) | e => do unwrapRegex (← delab e)

def delabRegex : Delab := do
  let e ← getExpr
  let fn ← if let Expr.const name _ := e.getAppFn' then pure name else return (← failure)
  match (fn, e.getAppArgs) with
  | (``Regex.bot, #[_]) => `([/⊥/])
  | (``Regex.empty, #[_]) => `([//])
  | (``Regex.unit, #[_, c]) => `([/ $(← unitRegex c) /])
  | (``Regex.string, #[w]) => match (← delab w) with
    | `($w:str) => `([/ $(← termRegex w) /])
    | _ => `(``Regex.string $(← delab w))
  | (``Regex.concat, #[_, q, r]) =>
    `([/ $(← exprRegex q) $(← exprRegex r) /])
  | (``Regex.or, #[_, q, r]) =>
    `([/ $(← exprRegex q) | $(← exprRegex r) /])
  | (``Regex.star, #[_, r]) => `([/ $(← exprRegex r) * /])
  | (``Regex.start, #[_]) => `([/⊢/])
  | (``Regex.end', #[_]) => `([/⊣/])
  | (``Regex.capture, #[_, n, r]) =>
    `([/ ($(← exprTerm' n) ← $(← exprRegex r) ) /])
  | (``Regex.backref, #[_, d, n]) => match d.getAppFn' with
    | Expr.const ``Regex.BackrefDefault.bot _ => `([/ \⊥ $(← exprTerm' n) /])
    | Expr.const ``Regex.BackrefDefault.empty _ => `([/ \ε $(← exprTerm' n) /])
    | d => `([/ \‹ $(← delab d) › $(← exprTerm' n) /])
  | _ => failure --throwError "unknown expression: {x}"

@[delab app.Regex.bot]         def delabBot         := delabRegex
@[delab app.Regex.empty]       def delabEmpty       := delabRegex
@[delab app.Regex.unit]        def delabUnit        := delabRegex
@[delab app.Regex.string]      def delabString      := delabRegex
@[delab app.Regex.concat]      def delabConcat      := delabRegex
@[delab app.Regex.or]          def delabOr          := delabRegex
@[delab app.Regex.star]        def delabStar        := delabRegex
@[delab app.Regex.start]       def delabStart       := delabRegex
@[delab app.Regex.end']        def delabEnd'        := delabRegex
@[delab app.Regex.capture]     def delabCapture     := delabRegex
@[delab app.Regex.backref]     def delabBackref     := delabRegex

@[category_parenthesizer regex]
def regex.parenthesizer : CategoryParenthesizer := Parenthesizer.term.parenthesizer

--def unexpRegex' : Unexpander
--  | `(``Regex.bot) => `(⊥)
--  | `(``empty) => `(«ε»)
--  | _ => throw ()
--
--@[app_unexpander bot]   def unexpBot   : Unexpander := unexpRegex'
--@[app_unexpander empty] def unexpEmpty : Unexpander := unexpRegex'

--def blah.bleh : Regex ℕ := empty
--def blah' : ℕ := 0
--#check [/`‹0›/]
--#check [/0/]
--#check [/(`‹0›)/]
--#check [/(0)/]

end Regex
