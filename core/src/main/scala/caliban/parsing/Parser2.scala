package caliban.parsing

import caliban.CalibanError.ParsingError
import caliban.InputValue
import caliban.InputValue._
import caliban.Value._
import caliban.parsing.adt.Definition._
import caliban.parsing.adt.Definition.ExecutableDefinition._
import caliban.parsing.adt.Definition.TypeSystemDefinition.DirectiveLocation._
import caliban.parsing.adt.Definition.TypeSystemDefinition._
import caliban.parsing.adt.Definition.TypeSystemDefinition.TypeDefinition._
import caliban.parsing.adt.Definition.TypeSystemExtension._
import caliban.parsing.adt.Definition.TypeSystemExtension.TypeExtension._
import caliban.parsing.adt.Selection._
import caliban.parsing.adt.Type._
import caliban.parsing.adt._
import cats.parse.{Numbers, Parser => P}
import cats.parse._
import zio.{IO, Task}

object Parser2 {
  private def sourceCharacter: P[Char]                      = P.charIn(Seq('\u0009', '\u000A','\u000D') ++ ('\u0020' to '\uFFFF'))
  private def sourceCharacterWithoutLineTerminator: P[Char] = P.charIn(Seq('\u0009')++ ('\u0020' to '\uFFFF'))

  private def witespace: Parser0[Unit] = P.charIn(' ', '\t', '\n', '\b', '\uFEFF').rep0.void
  private def wrapBrackets[T](t:Parser0[T]):P[T] = (P.char('{').surroundedBy(witespace)) *> t <* (P.char('}').surroundedBy(witespace))
  //private implicit val whitespace: P[_] => P[Unit] = ???
/*
  private implicit val whitespace: P[_] => P[Unit] = new (P[_] => P[Unit]) {

    type State = Int

    // statuses
    private final val Normal                  = 0
    private final val InsideLineComment       = 1
    private final val DetermineLineBreakStart = 2

    private final val UnicodeBOM   = '\uFEFF'
    private final val Tab          = '\u0009'
    private final val Space        = '\u0020'
    private final val LF           = '\u000A'
    private final val CR           = '\u000D'
    private final val Comma        = ','
    private final val CommentStart = '#'

    override def apply(p: P[_]): P[Unit] =
      loop(p.index, state = Normal)(p, p.input)

    @tailrec def loop(index: Int, state: State)(implicit ctx: P[_], input: ParserInput): ParsingRun[Unit] =
      if (input.isReachable(index)) {
        val currentChar = input(index)
        (state: @switch) match {
          case Normal =>
            (currentChar: @switch) match {
              case Space | LF | Comma | Tab | UnicodeBOM => loop(index + 1, state = Normal)
              case CommentStart                          => loop(index + 1, state = InsideLineComment)
              case CR                                    => loop(index + 1, state = DetermineLineBreakStart)
              case _                                     => ctx.freshSuccessUnit(index)
            }
          case InsideLineComment =>
            loop(
              index + 1,
              state = (currentChar: @switch) match {
                case CR => DetermineLineBreakStart
                case LF => Normal
                case _  => InsideLineComment
              }
            )
          case DetermineLineBreakStart =>
            (currentChar: @switch) match {
              case LF => loop(index + 1, state = Normal)
              case _  => loop(index, state = Normal)
            }
        }
      } else ctx.freshSuccessUnit(index)
  }
*/
  //private def name: P[String] = P.defer(P.charIn("_A-Za-z") ~~ P.charIn("_0-9A-Za-z").repX).!
  private def name:P[String] = (P.charIn(('a' to 'z') ++ ('A' to 'Z') ++ Seq('_')) ~ P.charIn(('a' to 'z') ++ ('A' to 'Z') ++ Seq('_') ++ ('0' to '9')).rep0).string


  private def booleanValue: P[BooleanValue] =
    P.string("true").as(BooleanValue(true)) | P.string("false").as(BooleanValue(false))

  //  private def negativeSign[_: P]: P[Unit] = P("-")
  //  private def nonZeroDigit[_: P]: P[Unit] = P(CharIn("1-9"))
  //  private def digit: P[Unit]        = P("0" | nonZeroDigit)
  //  private def integerPart: P[Unit]  = Numbers.signedIntString
  private def intValue: P[IntValue] = Numbers.signedIntString.map(IntValue(_))

  //  private def sign: P1[Char]              = P.charIn("-+")
  //  private def exponentIndicator: P1[Char] = P.charIn("eE")
  //  private def exponentPart: P[String]     = string((exponentIndicator ~ sign.? ~ Numbers.nonNegativeIntString))
  //  private def fractionalPart: P[String]   = ("." ~ Numbers.nonNegativeIntString).string

  private def floatValue: P[FloatValue] = Numbers.jsonNumber.map(FloatValue(_))

  //private def hexDigit: P[Char] = P.charIn("0-9a-fA-F")
  private def escapedUnicode: P[Char] =
    Rfc5234.hexdig.rep(4,4).string.map(Integer.parseInt(_, 16).toChar)

  private def escapedCharacter: P[Char] = P.charIn('\b', '\n', '\f', '\r', '\t')

  private def stringCharacter: P[Char] = {
    sourceCharacterWithoutLineTerminator.filter(c => c!='\"' && c!='\\') |
      (P.string("\\u")*> escapedUnicode) | (P.char('\\') *> escapedCharacter)
  }

  private def blockStringCharacter: P[String] = P.defer((P.string("\\\"\"\"").as("\"\"\""):P[String]) | (sourceCharacter.rep.string:P[String]))

  private def stringValue: P[StringValue] =
    P.defer(
      (P.string("\"\"\"") *> ((!P.string("\"\"\"")) *> blockStringCharacter).map(s => blockStringValue(s)) <* P.string("\"\"\""))|
        (P.string("\"") *> stringCharacter.rep.string <* P.string("\""))
    ).map(v => StringValue(v))

  private def blockStringValue(rawValue: String): String = {
    val l1 = rawValue.split("\r?\n").toList
    val commonIndent = l1 match {
      case Nil => None
      case _ :: tail =>
        tail.foldLeft(Option.empty[Int]) {
          case (commonIndent, line) =>
            val indent = "[ \t]*".r.findPrefixOf(line).fold(0)(_.length)
            if (indent < line.length && commonIndent.fold(true)(_ > indent)) Some(indent) else commonIndent
        }
    }
    // remove indentation
    val l2 = (commonIndent, l1) match {
      case (Some(value), head :: tail) => head :: tail.map(_.drop(value))
      case _                           => l1
    }
    // remove start lines that are only whitespaces
    val l3 = l2.dropWhile("[ \t]*".r.replaceAllIn(_, "").isEmpty)
    // remove end lines that are only whitespaces
    val l4 = l3.reverse.dropWhile("[ \t]*".r.replaceAllIn(_, "").isEmpty).reverse
    l4.mkString("\n")
  }

  private def nullValue: P[InputValue] = P.string("null").as(NullValue)
  private def enumValue: P[InputValue] = P.string(name).map(EnumValue)

  private def listValue: P[ListValue]  = P.defer(
    value.repSep0(P.char(',')).with1.between(P.char('['), P.char(']')).map(values => ListValue(values))
  )


  private def objectField: P[(String, InputValue)] = P.defer((name <* P.char(':')) ~ value)
  private def objectValue: P[ObjectValue] =
    objectField.rep0.with1.between(P.char('{'), P.char('}')).map(values => ObjectValue(values.toMap))

  private def value: P[InputValue] =
    P.defer(floatValue | intValue | booleanValue | stringValue | nullValue | enumValue | listValue | objectValue | variable)

  private def alias: P[String] = name <* P.char(':')

  private def argument: P[(String, InputValue)]     = P.defer((name <* P.char(':')) ~ value)
  private def arguments: P[Map[String, InputValue]] = P.defer(P.char('(') *> argument.rep <* P.char(')')).map(v => v.toList.toMap)

  private def directive: P[Directive] = P.defer((P.index.with1 <* P.char('@')) ~ name ~ arguments.?).map{ case ((index, name), arguments) =>
    Directive(name, arguments.getOrElse(Map()), index)
  }
  private def directives: P[List[Directive]] = P.defer(directive.rep).map(_.toList)

  private def selection: P[Selection]          = P.defer(field | fragmentSpread | inlineFragment)
  private def selectionSet: P[List[Selection]] =  wrapBrackets(selection.rep0).map(_.toList)

  private def namedType: P[NamedType] = name.filter(_ != "null").map(NamedType(_, nonNull = false))
  private def listType: P[ListType]  = type_.between(P.char('['),P.char(']')).map(t => ListType(t, nonNull = false))

  private def argumentDefinition: P[InputValueDefinition] =
    P.defer((stringValue.?.with1 ~ name <* P.char(':')) ~ type_ ~ (defaultValue.? ~ directives.?)).map {
      case (((description, name), type_), (defaultValue, directives)) =>
        InputValueDefinition(description.map(_.value), name, type_, defaultValue, directives.getOrElse(Nil))
    }
  private def argumentDefinitions: P[List[InputValueDefinition]] =
    P.defer( argumentDefinition.rep.between(P.char('('),P.char(')'))).map(_.toList)

  private def fieldDefinition: P[FieldDefinition] =
    P.defer((stringValue.?.with1 ~ name ~ argumentDefinitions.? <* P.char(':')) ~ type_ ~ directives.?).map {
      case ((((description, name), args), type_), directives) =>
        FieldDefinition(description.map(_.value), name, args.getOrElse(Nil), type_, directives.getOrElse(Nil))
    }

  private def nonNullType: P[Type] = P.defer((namedType | listType) <* P.char('!')).map {
    case t: NamedType => t.copy(nonNull = true)
    case t: ListType  => t.copy(nonNull = true)
  }
  private def type_ :P[Type] = P.defer(nonNullType | namedType | listType)

  private def variable: P[VariableValue] = (P.char('$')*> name).map(VariableValue)
  private def variableDefinitions: P[List[VariableDefinition]] = {
    P.defer(variableDefinition.rep.between(P.char('('),P.char(')'))).map(_.toList)
  }

  private def variableDefinition: P[VariableDefinition] =
    P.defer((variable <* P.char(':')) ~ type_ ~ defaultValue.? ~ directives).map {
      case (((v, t), default), dirs) => VariableDefinition(v.name, t, default, dirs)
    }

  private def defaultValue: P[InputValue] = P.char('=') *> value

  private def field: P[Field] = P.defer(((P.index ~ (alias.?)).with1 ~ name) ~ (arguments.? ~ directives.? ~ selectionSet.?)).map {
    case (((index, alias), name), ((args, dirs), sels)) =>
      Field(
        alias,
        name,
        args.getOrElse(Map()),
        dirs.getOrElse(Nil),
        sels.getOrElse(Nil),
        index
      )
  }

  private def fragmentName: P[String] = name.filter(_ != "on")

  private def fragmentSpread: P[FragmentSpread] = P.defer(P.string("...") *> fragmentName ~ directives).map {
    case (name, dirs) => FragmentSpread(name, dirs)
  }

  private def typeCondition: P[NamedType] = P.defer(P.string("on") *> namedType)

  private def inlineFragment: P[InlineFragment] = P.defer(P.string("...") *> typeCondition.?.with1 ~ directives ~ selectionSet).map {
    case ((typeCondition, dirs), sel) => InlineFragment(typeCondition, dirs, sel)
  }

  private def operationType: P[OperationType] =
    P.string("query").as(OperationType.Query) | P.string("mutation").as(OperationType.Mutation) | P.string("subscription").as(
      OperationType.Subscription
    )

  private def operationDefinition: P[OperationDefinition] =
    P.defer(operationType ~ (name.? ~ variableDefinitions.?) ~ directives ~ selectionSet).map {
      case (((operationType, (name, variableDefinitions)), directives), selection) =>
        OperationDefinition(operationType, name, variableDefinitions.getOrElse(Nil), directives, selection)
    } | P.defer(selectionSet).map(selection => OperationDefinition(OperationType.Query, None, Nil, Nil, selection))

  private def fragmentDefinition: P[FragmentDefinition] =
    P.defer(P.string("fragment") *> fragmentName ~ typeCondition ~ directives ~ selectionSet).map {
      case (((name, typeCondition), dirs), sel) => FragmentDefinition(name, typeCondition, dirs, sel)
    }

  private def objectTypeDefinition: P[ObjectTypeDefinition] =
    P.defer((stringValue.? <* P.string("type")).with1 ~ name ~ (implements.? ~ directives.?) ~  fieldDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case (((description, name), (implements, directives)), fields) =>
        ObjectTypeDefinition(
          description.map(_.value),
          name,
          implements.getOrElse(Nil),
          directives.getOrElse(Nil),
          fields.toList
        )
    }

  private def implements: P[List[NamedType]] = P.defer(P.string("implements") ~ P.char('&').? *> namedType ~ (P.char('&') *> namedType).rep).map {
    case (head, tail) => head :: tail.toList
  }

  private def interfaceTypeDefinition: P[InterfaceTypeDefinition] =
    P.defer(stringValue.?.with1 ~ (P.string("interface") *> name) ~ directives.? ~  fieldDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case (((description, name), directives), fields) =>
        InterfaceTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil), fields.toList)
    }

  private def inputObjectTypeDefinition: P[InputObjectTypeDefinition] =
    P.defer(stringValue.?.with1 ~ (P.string("input") *> name) ~ directives.? ~ argumentDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case (((description, name), directives), fields) =>
        InputObjectTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil), fields.toList)
    }

  private def enumValueDefinition: P[EnumValueDefinition] =
    P.defer(stringValue.?.with1 ~ name ~ directives.?).map {
      case ((description, enumValue), directives) =>
        EnumValueDefinition(description.map(_.value), enumValue, directives.getOrElse(Nil))
    }

  private def enumName: P[String] = name.filter(s => s != "true" && s != "false" && s != "null")

  private def enumTypeDefinition: P[EnumTypeDefinition] =
    P.defer(stringValue.?.with1 ~ (P.string("enum") *> enumName) ~ directives.? ~  enumValueDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case (((description, name), directives), enumValuesDefinition) =>
        EnumTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil), enumValuesDefinition.toList)
    }

  private def unionTypeDefinition: P[UnionTypeDefinition] =
    P.defer(stringValue.?.with1 ~ (P.string("union") *>name) ~ (directives.? <* P.char('=')) ~ (P.char('|').? *> namedType) ~ (P.char('|') *> namedType).rep).map {
      case ((((description, name), directives), m), ms) =>
        UnionTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil), (m :: ms.toList).map(_.name))
    }

  private def scalarTypeDefinition: P[ScalarTypeDefinition] =
    P.defer(stringValue.?.with1 ~ (P.string("scalar") *> name) ~ directives.?).map {
      case ((description, name), directives) =>
        ScalarTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil))
    }

  private def rootOperationTypeDefinition: P[(OperationType, NamedType)] = P.defer((operationType <* P.char(':')) ~ namedType)

  private def schemaDefinition: P[SchemaDefinition] =
    P.defer((P.string("schema") *> directives.?).with1 ~ rootOperationTypeDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case (directives, ops) =>
        val opsMap = ops.toList.toMap
        SchemaDefinition(
          directives.getOrElse(Nil),
          opsMap.get(OperationType.Query).map(_.name),
          opsMap.get(OperationType.Mutation).map(_.name),
          opsMap.get(OperationType.Subscription).map(_.name)
        )
    }

  private def schemaExtensionWithOptionalDirectivesAndOperations: P[SchemaExtension] =
    P.defer(directives.?.with1 ~  rootOperationTypeDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case (directives, ops) =>
        val opsMap = ops.toList.toMap
        SchemaExtension(
          directives.getOrElse(Nil),
          opsMap.get(OperationType.Query).map(_.name),
          opsMap.get(OperationType.Mutation).map(_.name),
          opsMap.get(OperationType.Subscription).map(_.name)
        )
    }

  private def schemaExtensionWithDirectives: P[SchemaExtension] =
    P.defer(directives).map(SchemaExtension(_, None, None, None))

  private def schemaExtension: P[SchemaExtension] =
    P.defer(P.string("extend schema") *> (schemaExtensionWithOptionalDirectivesAndOperations | schemaExtensionWithDirectives))

  private def scalarTypeExtension: P[ScalarTypeExtension] =
    P.defer(P.string("extend scalar") *> name ~ directives).map {
      case (name, directives) =>
        ScalarTypeExtension(name, directives)
    }

  private def objectTypeExtensionWithOptionalInterfacesOptionalDirectivesAndFields: P[ObjectTypeExtension] =
    P.defer(name ~ (implements.? ~ directives.?) ~ fieldDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case ((name, (implements, directives)), fields) =>
        ObjectTypeExtension(
          name,
          implements.getOrElse(Nil),
          directives.getOrElse(Nil),
          fields.toList
        )
    }

  private def objectTypeExtensionWithOptionalInterfacesAndDirectives: P[ObjectTypeExtension] =
    P.defer(name ~ implements.? ~ directives ~ (!fieldDefinition.rep.between(P.char('{'),P.char('}')))).map {
      case (((name, implements), directives),_) =>
        ObjectTypeExtension(
          name,
          implements.getOrElse(Nil),
          directives,
          Nil
        )
    }

  private def objectTypeExtensionWithInterfaces: P[ObjectTypeExtension] =
    P.defer(name ~ implements).map {
      case (name, implements) =>
        ObjectTypeExtension(
          name,
          implements,
          Nil,
          Nil
        )
    }

  private def objectTypeExtension: P[ObjectTypeExtension] =
    P.defer(
      P.string("extend type") *> (
        objectTypeExtensionWithOptionalInterfacesOptionalDirectivesAndFields orElse
          objectTypeExtensionWithOptionalInterfacesAndDirectives orElse
          objectTypeExtensionWithInterfaces
        )
    )

  private def interfaceTypeExtensionWithOptionalDirectivesAndFields: P[InterfaceTypeExtension] =
    P.defer(name ~ directives.? ~ fieldDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case ((name, directives), fields) =>
        InterfaceTypeExtension(name, directives.getOrElse(Nil), fields.toList)
    }

  private def interfaceTypeExtensionWithDirectives: P[InterfaceTypeExtension] =
    P.defer(name ~ directives).map {
      case (name, directives) =>
        InterfaceTypeExtension(name, directives, Nil)
    }

  private def interfaceTypeExtension: P[InterfaceTypeExtension] =
    P.defer(
      P.string("extend interface") *> (
        interfaceTypeExtensionWithOptionalDirectivesAndFields |
          interfaceTypeExtensionWithDirectives
        )
    )

  private def unionTypeExtensionWithOptionalDirectivesAndUnionMembers: P[UnionTypeExtension] =
    P.defer(name ~ (directives.? <* P.char('=')) ~ (P.char('|').? *> namedType) ~ (P.char('|') *> namedType).rep).map {
      case (((name, directives), m), ms) =>
        UnionTypeExtension(name, directives.getOrElse(Nil), (m :: ms.toList).map(_.name))
    }

  private def unionTypeExtensionWithDirectives: P[UnionTypeExtension] =
    P.defer(name ~ directives).map {
      case (name, directives) =>
        UnionTypeExtension(name, directives, Nil)
    }

  private def unionTypeExtension: P[UnionTypeExtension] =
    P.defer(P.string("extend union") *> (unionTypeExtensionWithOptionalDirectivesAndUnionMembers | unionTypeExtensionWithDirectives))

  private def enumTypeExtensionWithOptionalDirectivesAndValues: P[EnumTypeExtension] =
    P.defer(enumName ~ directives.? ~ enumValueDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case ((name, directives), enumValuesDefinition) =>
        EnumTypeExtension(name, directives.getOrElse(Nil), enumValuesDefinition.toList)
    }

  private def enumTypeExtensionWithDirectives: P[EnumTypeExtension] =
    P.defer(enumName ~ directives).map {
      case (name, directives) =>
        EnumTypeExtension(name, directives, Nil)
    }

  private def enumTypeExtension: P[EnumTypeExtension] =
    P.defer(P.string("extend enum") *> (enumTypeExtensionWithOptionalDirectivesAndValues | enumTypeExtensionWithDirectives))

  private def inputObjectTypeExtensionWithOptionalDirectivesAndFields: P[InputObjectTypeExtension] =
    P.defer(name ~ directives.? ~ argumentDefinition.rep.between(P.char('{'),P.char('}'))).map {
      case ((name, directives), fields) =>
        InputObjectTypeExtension(name, directives.getOrElse(Nil), fields.toList)
    }

  private def inputObjectTypeExtensionWithDirectives: P[InputObjectTypeExtension] =
    P.defer(name ~ directives).map {
      case (name, directives) =>
        InputObjectTypeExtension(name, directives, Nil)
    }

  private def inputObjectTypeExtension: P[InputObjectTypeExtension] =
    P.defer(
      P.string("extend input") *> (
        inputObjectTypeExtensionWithOptionalDirectivesAndFields orElse
          inputObjectTypeExtensionWithDirectives
        )
    )

  private def directiveLocation:P[DirectiveLocation] =
    P.defer(
      P.stringIn(Seq(
        "QUERY",
        "MUTATION",
        "SUBSCRIPTION",
        "FIELD",
        "FRAGMENT_DEFINITION",
        "FRAGMENT_SPREAD",
        "INLINE_FRAGMENT",
        "SCHEMA",
        "SCALAR",
        "OBJECT",
        "FIELD_DEFINITION",
        "ARGUMENT_DEFINITION",
        "INTERFACE",
        "UNION",
        "ENUM",
        "ENUM_VALUE",
        "INPUT_OBJECT",
        "INPUT_FIELD_DEFINITION"
      ))
    ).map {
      case "QUERY"                  => ExecutableDirectiveLocation.QUERY
      case "MUTATION"               => ExecutableDirectiveLocation.MUTATION
      case "SUBSCRIPTION"           => ExecutableDirectiveLocation.SUBSCRIPTION
      case "FIELD"                  => ExecutableDirectiveLocation.FIELD
      case "FRAGMENT_DEFINITION"    => ExecutableDirectiveLocation.FRAGMENT_DEFINITION
      case "FRAGMENT_SPREAD"        => ExecutableDirectiveLocation.FRAGMENT_SPREAD
      case "INLINE_FRAGMENT"        => ExecutableDirectiveLocation.INLINE_FRAGMENT
      case "SCHEMA"                 => TypeSystemDirectiveLocation.SCHEMA
      case "SCALAR"                 => TypeSystemDirectiveLocation.SCALAR
      case "OBJECT"                 => TypeSystemDirectiveLocation.OBJECT
      case "FIELD_DEFINITION"       => TypeSystemDirectiveLocation.FIELD_DEFINITION
      case "ARGUMENT_DEFINITION"    => TypeSystemDirectiveLocation.ARGUMENT_DEFINITION
      case "INTERFACE"              => TypeSystemDirectiveLocation.INTERFACE
      case "UNION"                  => TypeSystemDirectiveLocation.UNION
      case "ENUM"                   => TypeSystemDirectiveLocation.ENUM
      case "ENUM_VALUE"             => TypeSystemDirectiveLocation.ENUM_VALUE
      case "INPUT_OBJECT"           => TypeSystemDirectiveLocation.INPUT_OBJECT
      case "INPUT_FIELD_DEFINITION" => TypeSystemDirectiveLocation.INPUT_FIELD_DEFINITION
    }

  private def directiveDefinition: P[DirectiveDefinition] =
    P.defer(
      stringValue.?.with1 ~ (P.string("directive @") *> name) ~ (argumentDefinitions.? <* P.string("on")) ~ (P.char('|').? *> directiveLocation) ~ (P.char('|') *> directiveLocation).rep
    ).map {
      case ((((description, name), args), firstLoc), otherLoc) =>
        DirectiveDefinition(description.map(_.value), name, args.getOrElse(Nil), otherLoc.toList.toSet + firstLoc)
    }

  private def typeDefinition: P[TypeDefinition] =
    objectTypeDefinition orElse
      interfaceTypeDefinition orElse
      inputObjectTypeDefinition orElse
      enumTypeDefinition orElse
      unionTypeDefinition orElse
      scalarTypeDefinition

  private def typeSystemDefinition: P[TypeSystemDefinition] =
    typeDefinition orElse schemaDefinition orElse directiveDefinition

  private def executableDefinition: P[ExecutableDefinition] =
    P.defer(operationDefinition orElse fragmentDefinition)

  private def typeExtension: P[TypeExtension] =
    objectTypeExtension orElse
      interfaceTypeExtension orElse
      inputObjectTypeExtension orElse
      enumTypeExtension orElse
      unionTypeExtension orElse
      scalarTypeExtension

  private def typeSystemExtension: P[TypeSystemExtension] =
    schemaExtension orElse typeExtension

  private def definition: P[Definition] = executableDefinition orElse typeSystemDefinition orElse typeSystemExtension

  private def document: P[ParsedDocument] =
    P.defer((P.start.with1 *> definition.rep) <* P.end).map(seq => ParsedDocument(seq.toList))

  /**
   * Parses the given string into a [[caliban.parsing.adt.Document]] object or fails with a [[caliban.CalibanError.ParsingError]].
   */
  def parseQuery(query: String): IO[ParsingError, Document] = {
    val sm = SourceMapper(query)
    println("=====small====")
    println(field.parse(query))
    document.parse(query) match {
      case Left(error) =>
        println("============ERROR============")
        println(error)
        println(sm.getLocation(error.failedAtOffset))
        IO.fail(ParsingError(error.toString, Some(sm.getLocation(error.failedAtOffset))))
      case Right(result) =>
        println("===========SUCCESS==========")
        println(result)
        IO.succeed(Document(result._2.definitions,sm))
    }
//    Task(document.parse(query))
//      .mapError(ex => ParsingError(s"Internal parsing error", innerThrowable = Some(ex)))
//      .flatMap {
//      case Left(error) =>
//
//        IO.fail(ParsingError(error.toString, Some(sm.getLocation(error.failedAtOffset))))
//      case Right(result) =>
//
//        IO.succeed(Document(result._2.definitions,sm))
//    }
  }

  /**
   * Checks if the query is valid, if not returns an error string.
   */
  def check(query: String): Option[String] = document.parse(query) match {
    case Left(error) => Some(error.toString)
    case Right(_)    => None
  }
}
