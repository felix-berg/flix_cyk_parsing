trait Lexer[tok: Type] {
  type Err
  pub def lex(s: String): Option[List[tok]]
}

enum PredLogicToken with Eq, ToString {
  case Ident(Char),
  case LeftParen, 
  case RightParen,
  case And, case Or, case Implies,
  case Not,
  case Exists, case ForAll
  case Comma
}

def removeWhitespace(s: String): String = s |> String.replace({ src = " " }, { dst =  "" })

def getToken(reg: Regex, func: String -> PredLogicToken, s: String): Option[(PredLogicToken, String)] =
  Regex.getPrefix(reg, s) 
    |> Option.map(prefix -> (prefix, s |> String.drop(String.length(prefix))))
    |> Option.map(match (pref, suff) -> (func(pref), suff))

instance Lexer[PredLogicToken] {
  type Err = Unit

  pub def lex(s: String): Option[List[PredLogicToken]] = 
    use PredLogicToken.{ LeftParen, RightParen, Ident, And, Or, Not, Implies, Comma, Exists, ForAll };
    match String.isEmpty(s) {
      case true => Some(Nil)
      case _ => 
        let regexes: List[(Regex, String -> PredLogicToken)] = 
          (regex"\\(", (_ -> LeftParen)) ::
          (regex"\\)", (_ -> RightParen)) ::
          (regex"and|AND|∧", (_ -> And)) ::
          (regex"or|OR|∨", (_ -> Or)) ::
          (regex"implies|IMPLIES|->", (_ -> Implies)) ::
          (regex"not|NOT|¬", (_ -> Not)) ::
          (regex",", (_ -> Comma)) ::
          (regex"exists|∃", (_ -> Exists)) ::
          (regex"forall|∀", (_ -> ForAll)) ::
          (regex"[a-z]|[A-Z]", (str -> match String.toList(str) {
            case c :: Nil => Ident(c)
            case _ => ???
          })) :: Nil;
        regexes |> List.findMap(match (rgx, func) -> 
          getToken(rgx, func, s)
            |> Option.flatMap(match (tok, rest) -> 
              Lexer.lex(rest) |> Option.map(ts -> tok :: ts)
            )
        )
    }
}

def testLexer(): Unit \ IO = 
  use PredLogicToken.{ LeftParen, RightParen, Ident, And, Or, Not, Implies, Comma, Exists, ForAll };
  assertEq(Some(LeftParen :: Nil), Lexer.lex(removeWhitespace("(")));
  assertEq(Some(RightParen :: Nil), Lexer.lex(removeWhitespace(")")));
  assertEq(Some(Comma :: Nil), Lexer.lex(removeWhitespace(",")));
  assertEq(Some(List.repeat(2, And)), Lexer.lex(removeWhitespace("and ∧")));
  assertEq(Some(List.repeat(2, Or)), Lexer.lex(removeWhitespace("or ∨")));
  assertEq(Some(List.repeat(2, Implies)), Lexer.lex(removeWhitespace("implies ->")));
  assertEq(Some(List.repeat(2, Not)), Lexer.lex(removeWhitespace("not ¬")));
  assertEq(Some(List.repeat(2, Exists)), Lexer.lex(removeWhitespace("exists ∃")));
  assertEq(Some(List.repeat(2, ForAll)), Lexer.lex(removeWhitespace("forall ∀")));
  assertEq(Some(Ident('P') :: Nil), Lexer.lex(removeWhitespace("P")));
  assertEq(Some(Ident('c') :: Nil), Lexer.lex(removeWhitespace("c")));
  assertEq(
    Some(LeftParen :: RightParen :: And :: LeftParen :: And :: Ident('x') :: Nil), 
    Lexer.lex(removeWhitespace("( )and ( ∧ x"))
  )

enum Vars {
  case Atom
}

def main(): Unit \ IO = 
  testLexer();
  let grammar: Grammar[Vars, PredLogicToken] = Map#{};
  ???
