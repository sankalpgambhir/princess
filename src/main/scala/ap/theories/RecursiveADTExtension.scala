package ap.theories

import ap.parser._
import ap.parser.IExpression.v
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.types.MonoSortedIFunction
import ap.parser.IExpression.all
import ap.parser.SMTParsingUtils.asTerm
import ap.parser.SMTTypes.SMTType

class RecursiveADTExtension(
                            underlyingTheories: Seq[ADT],
                            recFun: IFunction,
                            body: ITerm
  ) extends SMTLinearisableTheory {

  val functions = List(recFun)

  // f(x) = body
  val definitionAxiom = {
    val (argSorts, resSort) = MonoSortedIFunction.functionType(recFun)
    val argNum = argSorts.size

    val argVars = for ((s, n) <- argSorts.zipWithIndex) yield v(argNum - n - 1, s)
    val resVar = v(argNum, resSort)
    val lhs = IFunApp(recFun, argVars)

    val recFunDefinition =
        all(argSorts.reverse ++ List(resSort),
                    ITrigger(Seq(lhs),
                      (lhs === body)
                    ))
    
    recFunDefinition
  }

  override val dependencies: Set[Theory] = {
    // Note: this should handle recursion correctly, by not knowing the theory
    // for the recursive call, and thus not adding it
    val collector = new TheoryCollector
    collector.apply(definitionAxiom)
    collector.theories.toSet ++ underlyingTheories
  }

  val (predicates, axioms, order, functionMap) = 
    Theory.genAxioms(
      theoryFunctions = List(recFun),
      theoryAxioms = definitionAxiom,
      otherTheories = dependencies.toSeq
    )

  val functionalPredicates = functionMap.get(recFun).toSet

  val functionPredicateMapping = functionMap.toSeq

  def plugin = None

  val totalityAxioms = Conjunction.TRUE

  // trigger other axioms based on recFun
  val triggerRelevantFunctions = Set.empty

  val predicateMatchConfig = Map.empty

  // if we find a model by unfolding this definition, it is indeed still a model
  override def isSoundForSat(theories: Seq[Theory], config: Theory.SatSoundnessConfig.Value): Boolean = {
    true
  }

  ////////////////////////////////////////////////////////////////////
  
  override def printSMTDeclaration: Unit = {
    // print the recFun's function declaration alone
    val ftype = MonoSortedIFunction.functionType(recFun)
    val formalArgs = ftype._1.zipWithIndex.map{ case (s, i) => s.newConstant(s"x!$i") }

    // TODO: actually, this needs a define-fun-rec
    SMTLineariser.printDefineFun(recFun, ftype, formalArgs, body)
  }
  
  ////////////////////////////////////////////////////////////////////

  TheoryRegistry.register(this)
  
}

