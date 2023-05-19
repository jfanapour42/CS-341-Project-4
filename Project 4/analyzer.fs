//
// Analyzer for simple C programs.  This component performs
// semantic analysis, in particular collecting variable
// names and their types. The analysis also checks to ensure
// variable names are unique --- no duplicates.
//
// If all is well, a "symbol table" is built and returned,
// containing all variables and their types. A symbol table
// is a list of tuples of the form (name, type).  Example:
//
//   [("x", "int"); ("y", "int"); ("z", "real")]
//
// Modified by:
//   Jordan Fanapour
//
// Original author:
//   Prof. Joe Hummel
//   U. of Illinois, Chicago
//   CS 341, Spring 2022
//

namespace compiler

module analyzer =
  //
  // NOTE: all functions in the module must be indented.
  //

  //
  // beginWith
  //
  let private beginWith (pattern: string) (token: string) =
    //
    // Checks if token starts with pattern
    // Returns true if so, false otherwise
    //
    let b = token.StartsWith (pattern)
    b

  //
  // containsSymbol returns true if symbol exists in symbolTable
  // (st)
  //
  let private containsSymbol symbol st =
    let l = List.filter (fun (id, t) -> id = symbol) st
    List.length l > 0

  //
  // getVar gets the variable name from token by ommitting     
  // identifier:
  //
  let private getVar (token: string) = 
    let id = token.[11..]
    id

  //
  // matchToken
  //
  let private matchToken expected_token (tokens: string list) =
    //
    // if the next token matches the expected token,  
    // keep parsing by returning the rest of the tokens.
    // Otherwise throw an exception because there's a 
    // syntax error, effectively stopping compilation
    // at the first error.
    //
    let next_token = List.head tokens

    if expected_token = "identifier" then
      if beginWith (expected_token) (next_token) = true then
        List.tail tokens
      else
        tokens
    else if expected_token = "int_literal" then
      if beginWith (expected_token) (next_token) = true then
        List.tail tokens
      else
        tokens
    else if expected_token = "real_literal" then
      if beginWith (expected_token) (next_token) = true then
        List.tail tokens
      else
        tokens
    else if expected_token = "str_literal" then
      if beginWith (expected_token) (next_token) = true then
        List.tail tokens
      else
        tokens
    else if expected_token = next_token then  
      List.tail tokens
    else
      tokens

  let rec private stmts tokens symbolTable = 
      let (t2, st2) = stmt tokens symbolTable
      let (t3, st3) = morestmts t2 st2
      (t3, st3)

  and private stmt tokens symbolTable =
    let next_token = List.head tokens
    if next_token = ";" then
      ((empty tokens), symbolTable)
    else if next_token = "int" ||
            next_token = "real" then
      vardecl tokens symbolTable
    else if next_token = "cin" then
      ((input tokens), symbolTable)
    else if next_token = "cout" then
      ((output tokens), symbolTable)
    else if beginWith "identifier" next_token = true then
      ((assignment tokens), symbolTable)
    else if next_token = "if" then
      ifstmt tokens symbolTable
    else
      (tokens, symbolTable)

  and private morestmts tokens symbolTable =
    if List.head tokens = "}" then
      (tokens, symbolTable)
    else
      let (t2, st2) = stmt tokens symbolTable
      let (t3, st3) = morestmts t2 st2
      (t3, st3)

  and private empty tokens =
    let t2 = matchToken ";" tokens
    t2

  and private vardecl tokens symbolTable =
    let next_token = List.head tokens
    if next_token = "int" then
      let idType = "int"
      let t2 = matchToken "int" tokens
      let id = getVar (List.head t2)
      if containsSymbol id symbolTable then
        failwith ("redefinition of variable '" + id + "'")
      else
        let symbol = (id, idType)
        let st2 = symbol::symbolTable
        let t3 = matchToken "identifier" t2
        let t4 = matchToken ";" t3
        (t4, st2)
    else if next_token = "real" then
      let idType = "real"
      let t2 = matchToken "real" tokens
      let id = getVar (List.head t2)
      if containsSymbol id symbolTable then
        failwith ("redefinition of variable '" + id + "'")
      else
        let symbol = (id, idType)
        let st2 = symbol::symbolTable
        let t3 = matchToken "identifier" t2
        let t4 = matchToken ";" t3
        (t4, st2)
    else
      (tokens, symbolTable)

  and private input tokens =
    let t2 = matchToken "cin" tokens
    let t3 = matchToken ">>" t2
    let t4 = matchToken "identifier" t3
    let t5 = matchToken ";" t4
    t5

  and private output tokens =
    let t2 = matchToken "cout" tokens
    let t3 = matchToken "<<" t2
    let t4 = output_value t3
    let t5 = matchToken ";" t4
    t5

  and private output_value tokens =
    let next_token = List.head tokens
    if next_token = "endl" then
      matchToken "endl" tokens
    else
      expr_value tokens

  and private assignment tokens =
    let t2 = matchToken "identifier" tokens
    let t3 = matchToken "=" t2
    let t4 = expr t3
    let t5 = matchToken ";" t4
    t5

  and private condition tokens =
    expr tokens

  and private then_part tokens symbolTable=
    stmt tokens symbolTable

  and private else_part tokens symbolTable =
    let next_token = List.head tokens
    if next_token = "else" then
      let t2 = matchToken "else" tokens
      stmt t2 symbolTable
    else
      (tokens, symbolTable)

  and private ifstmt tokens symbolTable = 
    let t2 = matchToken "if" tokens
    let t3 = matchToken "(" t2
    let t4 = condition t3
    let t5 = matchToken ")" t4
    let (t6, st2) = then_part t5 symbolTable
    let (t7, st3) = else_part t6 st2
    (t7, st3)

  and private expr tokens =
    let t2 = expr_value tokens
    //
    // now let's see if there's more to the expression:
    //
    let next_token = List.head t2
    //
    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then
      //
      let t3 = expr_op t2
      let t4 = expr_value t3
      t4
    else
      // just expr_value, that's it
      t2

  and private expr_value tokens =
    let next_token = List.head tokens
    if beginWith "identifier" next_token = true then
      matchToken "identifier" tokens
    else if beginWith "int_literal" next_token = true then
      matchToken "int_literal" tokens
    else if beginWith "real_literal" next_token = true then
      matchToken "real_literal" tokens
    else if beginWith "str_literal" next_token = true then
      matchToken "str_literal" tokens
    else if next_token = "true" then
      matchToken "true" tokens
    else if next_token = "false" then
      matchToken "false" tokens
    else
      tokens

  and private expr_op tokens = 
    let next_token = List.head tokens
    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then
      //
      matchToken next_token tokens
    else
      // error
      tokens

  let private simpleC tokens = 
    let t2 = matchToken "void" tokens
    let t3 = matchToken "main" t2
    let t4 = matchToken "(" t3
    let t5 = matchToken ")" t4
    let t6 = matchToken "{" t5
    let (t7, symbolTable) = stmts t6 []
    let t8 = matchToken "}" t7
    let t9 = matchToken "$" t8
    (t9, symbolTable)


  //
  // build_symboltable tokens
  //
  // Given a list of tokens, analyzes the program by looking
  // at variable declarations and collecting them into a
  // list. This list is known as a symbol table. Returns
  // a tuple (result, symboltable), where result is a string 
  // denoting "success" if valid, otherwise a string of the 
  // form "semantic_error:...".
  //
  // On success, the symboltable is a list of tuples of the
  // form (name, type), e.g. [("x","int"); ("y","real")]. On 
  // an error, the returned list is empty [].
  //
  let build_symboltable tokens = 
    try
      let (T2, symboltable) = simpleC tokens
      ("success", symboltable)
    with 
      | ex -> ("semantic_error: " + ex.Message, [])
