//
// Analyzer for simple C programs.  This component performs
// type checking.  The analyzer returns a string denoting
// success or failure. The string "success" if the input 
// program is legal, otherwise the string "type_error: ..." 
// is returned denoting an invalid simple C program.
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

module checker =
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
  // getVar gets the variable name from token by ommitting     
  // identifier:
  //
  let private getVar (token: string) = 
    let id = token.[11..]
    id

  //
  // getType gets the the stored type of id within the symbol
  // table
  //
  let private getType symbol st= 
    let l = List.filter (fun (id, t) -> id = symbol) st
    let (id, idType) = (List.head l)
    idType

  //
  // containsSymbol returns true if symbol exists in symbolTable
  // (st)
  //
  let private containsSymbol symbol st =
    let l = List.filter (fun (id, t) -> id = symbol) st
    List.length l > 0

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
        failwith ("expecting identifier, but found " + next_token)
    else if expected_token = "int_literal" then
      if beginWith (expected_token) (next_token) = true then
        List.tail tokens
      else
        failwith ("expecting int_literal, but found " + next_token)
    else if expected_token = "real_literal" then
      if beginWith (expected_token) (next_token) = true then
        List.tail tokens
      else
        failwith ("expecting real_literal, but found " + next_token)
    else if expected_token = "str_literal" then
      if beginWith (expected_token) (next_token) = true then
        List.tail tokens
      else
        failwith ("expecting str_literal, but found " + next_token)
    else if expected_token = next_token then  
      List.tail tokens
    else
      failwith ("expecting " + expected_token + ", but found " + next_token)

  let rec private stmts tokens symbolTable = 
      let t2 = stmt tokens symbolTable
      let t3 = morestmts t2 symbolTable
      t3

  and private stmt tokens symbolTable =
    let next_token = List.head tokens
    if next_token = ";" then
      empty tokens
    else if next_token = "int" ||
            next_token = "real" then
      vardecl tokens
    else if next_token = "cin" then
      input tokens symbolTable
    else if next_token = "cout" then
      output tokens symbolTable
    else if beginWith "identifier" next_token = true then
      assignment tokens symbolTable
    else if next_token = "if" then
      ifstmt tokens symbolTable
    else
      failwith("expecting statement, but found " + next_token)

  and private morestmts tokens symbolTable =
    if List.head tokens = "}" then
      tokens
    else
      let t2 = stmt tokens symbolTable
      let t3 = morestmts t2 symbolTable
      t3

  and private empty tokens =
    let t2 = matchToken ";" tokens
    t2

  and private vardecl tokens =
    let next_token = List.head tokens
    if next_token = "int" then
      let t2 = matchToken "int" tokens
      let t3 = matchToken "identifier" t2
      let t4 = matchToken ";" t3
      t4
    else if next_token = "real" then
      let t2 = matchToken "real" tokens
      let t3 = matchToken "identifier" t2
      let t4 = matchToken ";" t3
      t4
    else
      tokens

  and private input tokens symbolTable =
    let t2 = matchToken "cin" tokens
    let t3 = matchToken ">>" t2
    let id = getVar (List.head t3)
    if containsSymbol id symbolTable then
      let t4 = matchToken "identifier" t3
      let t5 = matchToken ";" t4
      t5
    else
      failwith ("variable '" + id + "' undefined")

  and private output tokens symbolTable =
    let t2 = matchToken "cout" tokens
    let t3 = matchToken "<<" t2
    let t4 = output_value t3 symbolTable
    let t5 = matchToken ";" t4
    t5

  and private output_value tokens symbolTable =
    let next_token = List.head tokens
    if next_token = "endl" then
      matchToken "endl" tokens
    else
      let (t2, idType) = expr_value tokens symbolTable
      t2

  and private assignment tokens symbolTable =
    let id = getVar (List.head tokens)
    if containsSymbol id symbolTable then
      let idType = getType id symbolTable
      let t2 = matchToken "identifier" tokens
      let t3 = matchToken "=" t2
      let (t4, exprType) = expr t3 symbolTable
      if (idType = exprType) || 
         (idType = "real" && exprType = "int") then
        let t5 = matchToken ";" t4
        t5
      else
        failwith ("cannot assign '" + exprType + "' to variable of type '" + idType + "'")
    else
      failwith ("variable '" + id + "' undefined")

  and private condition tokens symbolTable =
    let (t2, exprType) = expr tokens symbolTable
    if exprType = "bool" then
      t2
    else
      failwith ("if condition must be 'bool', but found '" + exprType + "'")

  and private then_part tokens symbolTable=
    stmt tokens symbolTable

  and private else_part tokens symbolTable =
    let next_token = List.head tokens
    if next_token = "else" then
      let t2 = matchToken "else" tokens
      stmt t2 symbolTable
    else
      tokens

  and private ifstmt tokens symbolTable = 
    let t2 = matchToken "if" tokens
    let t3 = matchToken "(" t2
    let t4 = condition t3 symbolTable
    let t5 = matchToken ")" t4
    let t6 = then_part t5 symbolTable
    let t7 = else_part t6 symbolTable
    t7

  and private expr tokens symbolTable =
    let (t2, idType1) = expr_value tokens symbolTable
    //
    // now let's see if there's more to the expression:
    //
    let next_token = List.head t2
    //
    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  then
      //
      let t3 = expr_op t2
      let (t4, idType2) = expr_value t3 symbolTable
      if (idType1 = "int" && idType2 = "int") ||
         (idType2 = "real" && idType2 = "real") then
        //
        (t4, idType1)
      else
        failwith ("operator " + next_token + " must involve 'int' or 'real'")
    else if next_token = "<"  ||
            next_token = "<=" ||
            next_token = ">"  ||
            next_token = ">=" ||
            next_token = "==" ||
            next_token = "!=" then
      //
      let t3 = expr_op t2
      let (t4, idType2) = expr_value t3 symbolTable
      if idType1 = idType2 then
        if idType1 = "real" && next_token = "==" then
          printfn "warning: comparing real numbers with == may never be true"
          (t4, "bool")
        else
          (t4, "bool")
      else
        failwith ("type mismatch '" + idType1 + "' " + next_token + " '" + idType2 + "'")
    else
      (t2, idType1)

  and private expr_value tokens symbolTable=
    let next_token = List.head tokens
    if beginWith "identifier" next_token = true then
      let id = getVar next_token
      if containsSymbol id symbolTable then
        let idType = getType id symbolTable
        let t2 = matchToken "identifier" tokens
        (t2, idType)
      else
        failwith ("variable '" + id + "' undefined")
    else if beginWith "int_literal" next_token = true then
      let t2 = matchToken "int_literal" tokens
      (t2, "int")
    else if beginWith "real_literal" next_token = true then
      let t2 = matchToken "real_literal" tokens
      (t2, "real")
    else if beginWith "str_literal" next_token = true then
      let t2 = matchToken "str_literal" tokens
      (t2, "str")
    else if next_token = "true" then
      let t2 = matchToken "true" tokens
      (t2, "bool")
    else if next_token = "false" then
      let t2 = matchToken "false" tokens
      (t2, "bool")
    else
      failwith("expecting identifier or literal, but found " + next_token)

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
      failwith ("expecting expression operator, but found " + next_token)

  let private simpleC tokens symboltable = 
    let t2 = matchToken "void" tokens
    let t3 = matchToken "main" t2
    let t4 = matchToken "(" t3
    let t5 = matchToken ")" t4
    let t6 = matchToken "{" t5
    let t7 = stmts t6 symboltable
    let t8 = matchToken "}" t7
    let t9 = matchToken "$" t8
    t9


  //
  // typecheck tokens symboltable
  //
  // Given a list of tokens and a symbol table, type-checks 
  // the program to ensure program's variables and expressions
  // are type-compatible. If the program is valid, returns 
  // the string "success". If the program contains a semantic
  // error or warning, returns a string of the form
  // "type_error: ...".
  //
  let typecheck tokens symboltable = 
    try
      let T2 = simpleC tokens symboltable
      "success"
    with 
      | ex -> "type_error: " + ex.Message

