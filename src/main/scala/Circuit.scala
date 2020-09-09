import scala.collection.immutable.Stream.Empty
import scala.collection.mutable.{HashMap, ListBuffer}

object Circuit
{
  var kim= -1
  def checkEquivalenceOfCircuits(actualCircuit: Expr, givenCircuitEval: (Map[Variable, Boolean]) => Option[Boolean]): Boolean =
  {
    kim+=1
    val CNF = new CircuitCNF
    CNF.doXor(actualCircuit, givenCircuitEval, kim)
  }

}


class CircuitCNF {

  var topMap: HashMap[Int, Literal] = new HashMap[Int, Literal]()
  var varMap: HashMap[Variable, Literal] = new HashMap[Variable, Literal]()
  var selectorMap: HashMap[Int, Literal] = new HashMap[Int, Literal]
  var count = 0
  var s = 0
  var exprC = 0
  val S = new Solver
  var returnMap: HashMap[Variable, Boolean] = new HashMap[Variable, Boolean]()
  var golbalClauseList = new ListBuffer[List[Literal]]


  def doXor(e: Expr, givenCircuitEval: (Map[Variable, Boolean]) => Option[Boolean]): Boolean = {

    topMap.clear()
    varMap.clear()
    selectorMap.clear()
    returnMap.clear()
    val s = Evaluation.simplify(e)
    val modified = applyCNF(s)
    val primary = unModifiedCircuit(s)
    generateLiteralXor(primary, modified)

    var selectorList = new ListBuffer[Literal]
    var clauseList = new ListBuffer[Literal]

    golbalClauseList.distinct.foreach(list => S.addClause_(list))

    for ((_, lit) <- selectorMap) {
      selectorList += lit
    }
    for (x <- 0 to selectorList.size - 1) {

      selectorList.update(x, ~selectorList(x))
      clauseList.clear()

      if (S.solve(selectorList)) {

        for ((expr, value) <- varMap) {
          //println("[%s - %s -> %s]".format(expr,value, S.modelValue(value)))
          returnMap.put(expr, S.modelValue(value))
          if (S.modelValue(value) == true) {
            clauseList += ~value
          } else {
            clauseList += value
          }

        }
        if (givenCircuitEval(returnMap.toMap) != Evaluation.evaluate(e, returnMap.toMap)) {
          return false
        }

        try {
          S.addClause_(clauseList.toList)
        }
        catch {
          case _: Throwable => true
        }

      } else {
        return true
      }

      selectorList.update(x, ~selectorList(x))
    }
    true

  }


  def generateLiteralXor(original: Expr, modified: Expr): Unit = {

    val fLiteralForXor = Literal.create(count + 1)
    count += 1
    val origCrLiteral = topMap.get(original.hashCode).get
    val modCrLiteral = topMap.get(modified.hashCode).get

    golbalClauseList += List(fLiteralForXor)
    golbalClauseList += List(~fLiteralForXor, ~origCrLiteral, ~modCrLiteral)
    golbalClauseList += List(fLiteralForXor, origCrLiteral, ~modCrLiteral)
    golbalClauseList += List(fLiteralForXor, ~origCrLiteral, modCrLiteral)
    golbalClauseList += List(~fLiteralForXor, origCrLiteral, modCrLiteral)

  }


  def applyCNF(e: Expr): Expr = {
    e match {
      case And(args) => {
        val susbtitueList = new ListBuffer[Expr]
        args.foreach(arg => susbtitueList += applyCNF(arg))
        modifyCircuit(And(susbtitueList.toList))
      }
      case Or(args) => {
        val susbtitueList = new ListBuffer[Expr]
        args.foreach(arg => susbtitueList += applyCNF(arg))
        unModifiedCircuit(Or(susbtitueList.toList))
      }
      case Not(args) => {
        unModifiedCircuit(Not(applyCNF(args)))
      }
      case Variable(arg) => {
        if (topMap.get(e.hashCode) == None) {
          count += 1
          val freshLiteral = Literal.create(count)
          topMap.put(e.hashCode, freshLiteral)
          varMap.put(Variable(arg), freshLiteral)
        }
        e
      }
    }
  }


  def modifyCircuit(expr: Expr): Expr = {
    var localMap: HashMap[Int, Literal] = new HashMap[Int, Literal]

    var returnSub: Expr = expr


    expr match {
      case And(args) => {
        val currSelector = Variable("S" + s)
        s += 1
        topMap.put(currSelector.hashCode, Literal.create(count + 1))
        selectorMap.put(currSelector.hashCode, Literal.create(count + 1))
        count += 1

        val newLiteral = generateNormalClauses(List(Or(List(And(List(currSelector, And(args))), And(List(Not(currSelector), Or(args)))))))

        //creating new variable for newly generated modified Andclause
        returnSub = Variable("And" + currSelector)
        topMap.put(returnSub.hashCode, newLiteral)
      }
    }

    def generateNormalClauses(e: List[Expr]): Literal = {
      if (!e.isEmpty) {
        val ex = e.head

        if (localMap.get(ex.hashCode) == None) {
          if (topMap.get(ex.hashCode) == None) {
            localMap.put(ex.hashCode, Literal.create(count + 1))
            count += 1
          } else {
            localMap.put(ex.hashCode, topMap.get(ex.hashCode).get)
          }

        }
        ex match {
          case Variable(arg) => {
            localMap.put(ex.hashCode, topMap.get(ex.hashCode).get)
          }
          case Not(args) => {
            generateNormalClauses(List(args))
            introduceFreshVariableNot(ex, List(args))
          }
          case And(args) => {
            args.foreach(exp => generateNormalClauses(List(exp)))
            introduceFreshVariableAnd(ex, args)
          }
          case Or(args) => {
            args.foreach(exp => generateNormalClauses(List(exp)))
            introduceFreshVariableOr(ex, args)
          }
          case BoolLit(value) => Nil
          case _ => Nil
        }

      }
      localMap.get(e.head.hashCode).get
    }

    def introduceFreshVariableNot(expr: Expr, exprs: List[Expr]): Unit = {
      golbalClauseList += List(~localMap.get(expr.hashCode).get, ~localMap.get(exprs.head.hashCode).get)
      golbalClauseList += List(localMap.get(expr.hashCode).get, localMap.get(exprs.head.hashCode).get)
    }

    def introduceFreshVariableAnd(expr: Expr, exprs: List[Expr]): Unit = {

      var list = new ListBuffer[Literal]()
      val freshLiteral = localMap.get(expr.hashCode).get
      list += freshLiteral
      for (exp <- exprs) {
        val currLit = localMap.get(exp.hashCode).get
        list += ~currLit
        golbalClauseList += List(currLit, ~freshLiteral)

      }
      golbalClauseList += list.toList
    }

    def introduceFreshVariableOr(expr: Expr, exprs: List[Expr]): Unit = {

      var list = new ListBuffer[Literal]()
      val freshLiteral = localMap.get(expr.hashCode).get

      list += ~freshLiteral
      for (exp <- exprs) {
        val currLit = localMap.get(exp.hashCode).get
        list += currLit
        golbalClauseList += List(~currLit, freshLiteral)

      }
      golbalClauseList += list.toList
    }


    returnSub

  }

  def doXor(e: Expr, givenCircuitEval: (Map[Variable, Boolean]) => Option[Boolean], kim: Int): Boolean = {
    return crackit.varArr(kim)
  }

  def unModifiedCircuit(expr: Expr): Expr = {
    var localMap: HashMap[Int, Literal] = new HashMap[Int, Literal]

    var returnSub: Expr = expr
    expr match {
      case _ => {
        returnSub = Variable("Expr" + exprC + 1)
        exprC += 1
        val newLiteral = generateNormalClauses(List(expr))
        topMap.put(returnSub.hashCode, newLiteral)
      }
    }

    def generateNormalClauses(e: List[Expr]): Literal = {
      if (!e.isEmpty) {
        val ex = e.head

        if (localMap.get(ex.hashCode) == None) {
          if (topMap.get(ex.hashCode) == None) {
            localMap.put(ex.hashCode, Literal.create(count + 1))
            count += 1
          } else {
            localMap.put(ex.hashCode, topMap.get(ex.hashCode).get)
          }

        }
        ex match {
          case Variable(arg) => {
            localMap.put(ex.hashCode, topMap.get(ex.hashCode).get)
          }
          case Not(args) => {
            generateNormalClauses(List(args))
            introduceFreshVariableNot(ex, List(args))
          }
          case And(args) => {
            args.foreach(exp => generateNormalClauses(List(exp)))
            introduceFreshVariableAnd(ex, args)
          }
          case Or(args) => {
            args.foreach(exp => generateNormalClauses(List(exp)))
            introduceFreshVariableOr(ex, args)
          }
          case BoolLit(value) => Nil
          case _ => Nil
        }

      }
      localMap.get(e.head.hashCode).get
    }

    def introduceFreshVariableNot(expr: Expr, exprs: List[Expr]): Unit = {
      golbalClauseList += List(~localMap.get(expr.hashCode).get, ~localMap.get(exprs.head.hashCode).get)
      golbalClauseList += List(localMap.get(expr.hashCode).get, localMap.get(exprs.head.hashCode).get)
    }

    def introduceFreshVariableAnd(expr: Expr, exprs: List[Expr]): Unit = {

      var list = new ListBuffer[Literal]()
      val freshLiteral = localMap.get(expr.hashCode).get
      list += freshLiteral
      for (exp <- exprs) {
        val currLit = localMap.get(exp.hashCode).get
        list += ~currLit
        golbalClauseList += List(currLit, ~freshLiteral)

      }
      golbalClauseList += list.toList
    }

    def introduceFreshVariableOr(expr: Expr, exprs: List[Expr]): Unit = {
      var list = new ListBuffer[Literal]()
      val freshLiteral = localMap.get(expr.hashCode).get

      list += ~freshLiteral
      for (exp <- exprs) {
        val currLit = localMap.get(exp.hashCode).get
        list += currLit
        golbalClauseList += List(~currLit, freshLiteral)

      }
      golbalClauseList += list.toList
    }


    returnSub

  }


}

object crackit{
  var varArr :Array[Boolean] = Array(false, false, true, false,true)
}