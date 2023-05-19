//
// Parser for simple C programs.  This component checks 
// the input program to see if it meets the syntax rules
// of simple C.  The parser returns a string denoting
// success or failure. 
//
// Returns: the string "success" if the input program is
// legal, otherwise the string "syntax_error: ..." is
// returned denoting an invalid simple C program.
//
// Jordan Fanapour
//
// Original author:
//   Prof. Joe Hummel
//   U. of Illinois, Chicago
//   CS 341, Spring 2022
//

namespace compiler

module parser =
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

  let rec private stmts tokens = 
      let t2 = stmt tokens
      let t3 = morestmts t2
      t3

  and private stmt tokens =
    let next_token = List.head tokens
    if next_token = ";" then
      empty tokens
    else if next_token = "int" ||
            next_token = "real" then
      vardecl tokens
    else if next_token = "cin" then
      input tokens
    else if next_token = "cout" then
      output tokens
    else if beginWith "identifier" next_token = true then
      assignment tokens
    else if next_token = "if" then
      ifstmt tokens
    else
      failwith("expecting statement, but found " + next_token)

  and private morestmts tokens =
    if List.head tokens = "}" then
      tokens
    else
      let t2 = stmt tokens
      let t3 = morestmts t2
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

  and private then_part tokens =
    stmt tokens

  and private else_part tokens =
    let next_token = List.head tokens
    if next_token = "else" then
      let t2 = matchToken "else" tokens
      stmt t2
    else
      tokens

  and private ifstmt tokens = 
    let t2 = matchToken "if" tokens
    let t3 = matchToken "(" t2
    let t4 = condition t3
    let t5 = matchToken ")" t4
    let t6 = then_part t5
    let t7 = else_part t6
    t7

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
      let T2 = matchToken next_token tokens
      T2
    else
      // error
      failwith ("expecting expression operator, but found " + next_token)

  //
  // simpleC
  //
  let private simpleC tokens = 
    let t2 = matchToken "void" tokens
    let t3 = matchToken "main" t2
    let t4 = matchToken "(" t3
    let t5 = matchToken ")" t4
    let t6 = matchToken "{" t5
    let t7 = stmts t6
    let t8 = matchToken "}" t7
    let t9 = matchToken "$" t8
    t9

  //
  // parse tokens
  //
  // Given a list of tokens, parses the list and determines
  // if the list represents a valid simple C program.  Returns
  // the string "success" if valid, otherwise returns a 
  // string of the form "syntax_error:...".
  //
  let parse tokens = 
    try
      let result = simpleC tokens
      "success"
    with 
      | ex -> "syntax_error: " + ex.Message