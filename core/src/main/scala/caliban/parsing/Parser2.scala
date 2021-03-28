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

  private final val UnicodeBOM   = '\uFEFF'
  private final val Tab          = '\u0009'
  private final val Space        = '\u0020'
  private final val LF           = '\u000A'
  private final val CR           = '\u000D'
  private final val Comma        = ','
  private def whitespace: Parser[_] = P.charIn(UnicodeBOM, Tab, Space, LF, CR, Comma)
  private def comment:Parser[_] = P.charIn('#') ~ P.until(P.char(LF)|P.string(s"$CR$LF"))
  private def whitespaceWithComment = (whitespace | comment).rep0.void
  private def whitespaces:Parser0[Unit] =  whitespace.rep0.void
  private def wrapBrackets[T](t:Parser0[T]):P[T] = P.char('{').surroundedBy(whitespaceWithComment) *> t <* (P.char('}').surroundedBy(whitespaceWithComment))
  private def wrapParentheses[T](t:Parser0[T]):P[T] = P.char('(').surroundedBy(whitespaceWithComment) *> t <* (P.char(')').surroundedBy(whitespaceWithComment))
  private def wrapSquareBrackets[T](t:Parser0[T]):P[T] = P.char('[').surroundedBy(whitespaceWithComment) *> t <* (P.char(']').surroundedBy(whitespaceWithComment))
  private def wrapWhitespaces[T](t:Parser[T]):P[T] = t.surroundedBy(whitespaceWithComment)
  private def wrapWhitespaces0[T](t:Parser0[T]):Parser0[T]= t.surroundedBy(whitespaceWithComment)

  private object StringUtil {
    private val decodeTable: Map[Char, Char] = Map(
      ('\\', '\\'),
      ('\'', '\''),
      ('\"', '\"'),
      ('b', 8.toChar), // backspace
      ('f', 12.toChar), // form-feed
      ('n', '\n'),
      ('r', '\r'),
      ('t', '\t')
    )

    private val encodeTable = decodeTable.iterator.map { case (v, k) => (k, s"\\$v") }.toMap

    private val nonPrintEscape: Array[String] =
      (0 until 32).map { c =>
        val strHex = c.toHexString
        val strPad = List.fill(4 - strHex.length)('0').mkString
        s"\\u$strPad$strHex"
      }.toArray

    val escapedToken: P[Unit] = {
      val escapes = P.charIn(decodeTable.keys.toSeq)

      val oct = P.charIn('0' to '7')
      val octP = P.char('o') ~ oct ~ oct

      val hex = P.charIn(('0' to '9') ++ ('a' to 'f') ++ ('A' to 'F'))
      val hex2 = hex ~ hex
      val hexP = P.char('x') ~ hex2

      val hex4 = hex2 ~ hex2
      val u4 = P.char('u') ~ hex4
      val hex8 = hex4 ~ hex4
      val u8 = P.char('U') ~ hex8

      val after = P.oneOf[Any](escapes :: octP :: hexP :: u4 :: u8 :: Nil)
      (P.char('\\') ~ after).void
    }

    /** String content without the delimiter
     */
    def undelimitedString(endP: P[Unit]): P[String] =
      escapedToken.backtrack
        .orElse((!endP).with1 ~ P.anyChar)
        .rep
        .string
        .flatMap { str =>
          unescape(str) match {
            case Right(str1) => P.pure(str1)
            case Left(_) => P.fail
          }
        }

    private val simpleString: Parser0[String] =
      P.charsWhile0(c => c >= ' ' && c != '"' && c != '\\')

    def escapedString(q: Char): P[String] = {
      val end: P[Unit] = P.char(q)
      end *> ((simpleString <* end).backtrack
        .orElse(undelimitedString(end) <* end))
    }
    def escape(quoteChar: Char, str: String): String = {
      // We can ignore escaping the opposite character used for the string
      // x isn't escaped anyway and is kind of a hack here
      val ignoreEscape = if (quoteChar == '\'') '"' else if (quoteChar == '"') '\'' else 'x'
      str.flatMap { c =>
        if (c == ignoreEscape) c.toString
        else
          encodeTable.get(c) match {
            case None =>
              if (c < ' ') nonPrintEscape(c.toInt)
              else c.toString
            case Some(esc) => esc
          }
      }
    }

    def unescape(str: String): Either[Int, String] = {
      val sb = new java.lang.StringBuilder
      def decodeNum(idx: Int, size: Int, base: Int): Int = {
        val end = idx + size
        if (end <= str.length) {
          val intStr = str.substring(idx, end)
          val asInt =
            try Integer.parseInt(intStr, base)
            catch { case _: NumberFormatException => ~idx }
          sb.append(asInt.toChar)
          end
        } else ~(str.length)
      }
      @annotation.tailrec
      def loop(idx: Int): Int =
        if (idx >= str.length) {
          // done
          idx
        } else if (idx < 0) {
          // error from decodeNum
          idx
        } else {
          val c0 = str.charAt(idx)
          if (c0 != '\\') {
            sb.append(c0)
            loop(idx + 1)
          } else {
            // str(idx) == \
            val nextIdx = idx + 1
            if (nextIdx >= str.length) {
              // error we expect there to be a character after \
              ~idx
            } else {
              val c = str.charAt(nextIdx)
              decodeTable.get(c) match {
                case Some(d) =>
                  sb.append(d)
                  loop(idx + 2)
                case None =>
                  c match {
                    case 'o' => loop(decodeNum(idx + 2, 2, 8))
                    case 'x' => loop(decodeNum(idx + 2, 2, 16))
                    case 'u' => loop(decodeNum(idx + 2, 4, 16))
                    case 'U' => loop(decodeNum(idx + 2, 8, 16))
                    case other =>
                      // \c is interpretted as just \c, if the character isn't escaped
                      sb.append('\\')
                      sb.append(other)
                      loop(idx + 2)
                  }
              }
            }
          }
        }

      val res = loop(0)
      if (res < 0) Left(~res)
      else Right(sb.toString)
    }
  }

  private def name:P[String] = (P.charIn(('a' to 'z') ++ ('A' to 'Z') ++ Seq('_')) ~ P.charIn(('a' to 'z') ++ ('A' to 'Z') ++ Seq('_') ++ ('0' to '9')).rep0).string


  private def booleanValue: P[BooleanValue] =
    P.string("true").as(BooleanValue(true)) | P.string("false").as(BooleanValue(false))

  private def intValue: P[IntValue] = (Numbers.signedIntString <* (!P.char('.')).void).backtrack.map(IntValue(_))

  private def floatValue: P[FloatValue] = Numbers.jsonNumber.map(FloatValue(_))

  private def stringValue: P[StringValue] =
    P.defer(
      (P.string("\"\"\"") *> StringUtil.undelimitedString(P.string("\"\"\"")).map(blockStringValue)<* P.string("\"\"\"")) |
      StringUtil.escapedString('\"')
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
    wrapSquareBrackets(value.repSep0(whitespaceWithComment)).map(values => ListValue(values))
  )


  private def objectField: P[(String, InputValue)] = P.defer((name <* wrapWhitespaces(P.char(':'))) ~ value)
  private def objectValue: P[ObjectValue] = P.defer(
    wrapBrackets(objectField.rep0).map(values => ObjectValue(values.toMap))
  )

  private def value: P[InputValue] =
    P.defer(P.oneOf(List(intValue, floatValue, booleanValue, stringValue, nullValue, enumValue, listValue, objectValue, variable)))

  private def alias: P[String] = name <* wrapWhitespaces(P.char(':'))

  private def argument: P[(String, InputValue)]     = P.defer((name <* wrapWhitespaces(P.char(':'))) ~ value)
  private def arguments: P[Map[String, InputValue]] = wrapParentheses(argument.repSep0(whitespaceWithComment)).map(v => v.toMap)

  private def directive: P[Directive] = P.defer(wrapWhitespaces(P.index.with1 <* P.char('@')).backtrack ~ name ~ arguments.backtrack.?).map{ case ((index, name), arguments) =>
    Directive(name, arguments.getOrElse(Map()), index)
  }
  private def directives: P[List[Directive]] = P.defer(directive.rep).map(_.toList)

  private def selection: P[Selection]          = P.defer(wrapWhitespaces(field | fragmentSpread | inlineFragment))
  private def selectionSet: P[List[Selection]] =  wrapBrackets(selection.rep0).map(_.toList)

  private def namedType: P[NamedType] = name.filter(_ != "null").map(NamedType(_, nonNull = false))
  private def listType: P[ListType]  = wrapSquareBrackets(type_).map(t => ListType(t, nonNull = false))

  private def argumentDefinition: P[InputValueDefinition] =
    P.defer((stringValue.backtrack.?.with1 ~ name <* wrapWhitespaces(P.char(':'))) ~ type_ ~ (defaultValue.backtrack.? ~ directives.backtrack.?)).map {
      case (((description, name), type_), (defaultValue, directives)) =>
        InputValueDefinition(description.map(_.value), name, type_, defaultValue, directives.getOrElse(Nil))
    }
  private def argumentDefinitions: P[List[InputValueDefinition]] =
    P.defer(wrapParentheses(argumentDefinition.rep)).map(_.toList)

  private def fieldDefinition: P[FieldDefinition] =
    P.defer((wrapWhitespaces(stringValue).backtrack.?.with1 ~ name ~ argumentDefinitions.? <* wrapWhitespaces(P.char(':'))) ~ type_ ~ directives.backtrack.?).map {
      case ((((description, name), args), type_), directives) =>
        FieldDefinition(description.map(_.value), name, args.getOrElse(Nil), type_, directives.getOrElse(Nil))
    }

  private def nonNullType: P[Type] = P.defer(((namedType | listType) <* P.char('!')).backtrack).map {
    case t: NamedType => t.copy(nonNull = true)
    case t: ListType  => t.copy(nonNull = true)
  }
  private def type_ :P[Type] = P.defer(nonNullType | namedType | listType)

  private def variable: P[VariableValue] = (P.char('$')*>name).map(VariableValue)
  private def variableDefinitions: P[List[VariableDefinition]] = {
    P.defer(wrapParentheses(variableDefinition.repSep0(whitespaceWithComment)))//.map(_.toList)
  }

  private def variableDefinition: P[VariableDefinition] =
    P.defer((variable <* wrapWhitespaces(P.char(':'))) ~ type_ ~ (defaultValue.backtrack.? ~ directives.backtrack.?)).map {
      case ((v, t), (default, dirs)) => VariableDefinition(v.name, t, default, dirs.getOrElse(Nil))
    }

  private def defaultValue: P[InputValue] = wrapWhitespaces(P.char('=')) *> value

  private def field: P[Field] = P.defer(((P.index ~ alias.backtrack.?).with1 ~ name) ~ (arguments.backtrack.? ~ directives.backtrack.? ~ selectionSet.backtrack.?)).map {
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

//  private def fragmentSpread: P[FragmentSpread] = P.defer(P.string("...") *> fragmentName ~ directives).map {
//    case (name, dirs) => FragmentSpread(name, dirs)
//  }

  private def fragmentSpread: P[FragmentSpread] = P.defer((P.string("...") *> fragmentName).backtrack ~ directives.backtrack.?).map {
    case (name, dirs) => FragmentSpread(name, dirs.getOrElse(Nil))
  }

  private def typeCondition: P[NamedType] = P.defer(wrapWhitespaces(P.string("on")) *> namedType)

  private def inlineFragment: P[InlineFragment] = P.defer(wrapWhitespaces(P.string("...")) *> typeCondition.? ~ directives.backtrack.? ~ selectionSet).map {
    case ((typeCondition, dirs), sel) => InlineFragment(typeCondition, dirs.getOrElse(Nil), sel)
  }

  private def operationType: P[OperationType] =
    wrapWhitespaces(P.string("query").as(OperationType.Query) | P.string("mutation").as(OperationType.Mutation) | P.string("subscription").as(
      OperationType.Subscription
    ))

  private def operationDefinition: P[OperationDefinition] =
    (P.defer(operationType.backtrack ~ (name.backtrack.? ~ variableDefinitions.backtrack.?) ~ directives.backtrack.? ~ selectionSet).map {
      case (((operationType, (name, variableDefinitions)), directives), selection) =>
        OperationDefinition(operationType, name, variableDefinitions.getOrElse(Nil), directives.getOrElse(Nil), selection)
    } orElse P.defer(selectionSet.backtrack).map(selection => OperationDefinition(OperationType.Query, None, Nil, Nil, selection)))

  private def fragmentDefinition: P[FragmentDefinition] =
    P.defer(wrapWhitespaces(P.string("fragment")).backtrack *> fragmentName ~ typeCondition ~ directives.backtrack.? ~ selectionSet).map {
      case (((name, typeCondition), dirs), sel) => FragmentDefinition(name, typeCondition, dirs.getOrElse(Nil), sel)
    }

  private def objectTypeDefinition: P[ObjectTypeDefinition] =
    P.defer((stringValue.backtrack.? <* wrapWhitespaces(P.string("type"))).backtrack.with1 ~ name ~ (implements.backtrack.? ~ directives.backtrack.?) ~  wrapBrackets(fieldDefinition.repSep0(whitespaceWithComment))).map {
      case (((description, name), (implements, directives)), fields) =>
        ObjectTypeDefinition(
          description.map(_.value),
          name,
          implements.getOrElse(Nil),
          directives.getOrElse(Nil),
          fields
        )
    }

  private def implements: P[List[NamedType]] = P.defer(wrapWhitespaces(P.string("implements")).backtrack ~ wrapWhitespaces(P.char('&')).backtrack.? *> namedType ~ (wrapWhitespaces(P.char('&')).backtrack *> namedType).rep0).map {
    case (head, tail) => head :: tail
  }

  private def interfaceTypeDefinition: P[InterfaceTypeDefinition] =
    P.defer(stringValue.backtrack.?.with1 ~ (P.string("interface").backtrack *> name) ~ directives.backtrack.? ~  wrapBrackets(fieldDefinition.repSep0(whitespaceWithComment))).map {
      case (((description, name), directives), fields) =>
        InterfaceTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil), fields)
    }

  private def inputObjectTypeDefinition: P[InputObjectTypeDefinition] =
    P.defer(stringValue.backtrack.?.with1 ~ (P.string("input").backtrack *> name) ~ directives.backtrack.? ~ wrapBrackets(argumentDefinition.rep0)).map {
      case (((description, name), directives), fields) =>
        InputObjectTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil), fields)
    }

  private def enumValueDefinition: P[EnumValueDefinition] =
    P.defer(stringValue.backtrack.?.with1 ~ name ~ directives.backtrack.?).map {
      case ((description, enumValue), directives) =>
        EnumValueDefinition(description.map(_.value), enumValue, directives.getOrElse(Nil))
    }

  private def enumName: P[String] = name.filter(s => s != "true" && s != "false" && s != "null")

  private def enumTypeDefinition: P[EnumTypeDefinition] =
    P.defer(stringValue.backtrack.?.with1 ~ (P.string("enum").backtrack *> enumName) ~ directives.? ~  wrapBrackets(enumValueDefinition.repSep0(whitespaceWithComment))).map {
      case (((description, name), directives), enumValuesDefinition) =>
        EnumTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil), enumValuesDefinition)
    }

  private def unionTypeDefinition: P[UnionTypeDefinition] =
    P.defer(stringValue.backtrack.?.with1 ~ (P.string("union").backtrack *>name) ~ (directives.? <* P.char('=')) ~ (P.char('|').? *> namedType) ~ (P.char('|') *> namedType).rep).map {
      case ((((description, name), directives), m), ms) =>
        UnionTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil), (m :: ms.toList).map(_.name))
    }

  private def scalarTypeDefinition: P[ScalarTypeDefinition] =
    P.defer(stringValue.backtrack.?.with1 ~ (P.string("scalar").backtrack *> name) ~ directives.?).map {
      case ((description, name), directives) =>
        ScalarTypeDefinition(description.map(_.value), name, directives.getOrElse(Nil))
    }

  private def rootOperationTypeDefinition: P[(OperationType, NamedType)] = P.defer((operationType <* wrapWhitespaces(P.char(':'))) ~ namedType)

  private def schemaDefinition: P[SchemaDefinition] =
    P.defer((P.string("schema") *> directives.backtrack.?).with1 ~ wrapBrackets(rootOperationTypeDefinition.repSep0(whitespaceWithComment))).map {
      case (directives, ops) =>
        val opsMap = ops.toMap
        SchemaDefinition(
          directives.getOrElse(Nil),
          opsMap.get(OperationType.Query).map(_.name),
          opsMap.get(OperationType.Mutation).map(_.name),
          opsMap.get(OperationType.Subscription).map(_.name)
        )
    }

  private def schemaExtensionWithOptionalDirectivesAndOperations: Parser0[SchemaExtension] =
    P.defer0(directives.backtrack.? ~ wrapBrackets(rootOperationTypeDefinition.repSep0(whitespaceWithComment)).backtrack.?).map {
      case (directives, ops) =>
        val opsMap = ops.getOrElse(Nil).toMap
        SchemaExtension(
          directives.getOrElse(Nil),
          opsMap.get(OperationType.Query).map(_.name),
          opsMap.get(OperationType.Mutation).map(_.name),
          opsMap.get(OperationType.Subscription).map(_.name)
        )
    }

  private def schemaExtension: P[SchemaExtension] =
    P.defer(wrapWhitespaces(P.string("extend schema")).backtrack *> schemaExtensionWithOptionalDirectivesAndOperations)

  private def scalarTypeExtension: P[ScalarTypeExtension] =
    P.defer(wrapWhitespaces(P.string("extend scalar")).backtrack *> name ~ directives).map {
      case (name, directives) =>
        ScalarTypeExtension(name, directives)
    }

  private def objectTypeExtensionWithOptionalInterfacesOptionalDirectivesAndFields: P[ObjectTypeExtension] =
    P.defer(name ~ (implements.backtrack.? ~ directives.backtrack.?) ~ wrapBrackets(fieldDefinition.repSep0(whitespaceWithComment)).backtrack.?).map {
      case ((name, (implements, directives)), fields) =>
        ObjectTypeExtension(
          name,
          implements.getOrElse(Nil),
          directives.getOrElse(Nil),
          fields.getOrElse(Nil)
        )
    }

  private def objectTypeExtensionWithOptionalInterfacesAndDirectives: P[ObjectTypeExtension] =
    P.defer(name.backtrack ~ implements.backtrack.? ~ directives.backtrack ~ (!wrapBrackets(fieldDefinition.repSep0(whitespaceWithComment)))).map {
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
      wrapWhitespaces(P.string("extend type")).backtrack *> (
        objectTypeExtensionWithOptionalInterfacesOptionalDirectivesAndFields // orElse
//          objectTypeExtensionWithOptionalInterfacesAndDirectives orElse
//          objectTypeExtensionWithInterfaces
        )
    )

  private def interfaceTypeExtensionWithOptionalDirectivesAndFields: P[InterfaceTypeExtension] =
    P.defer(name ~ (directives.backtrack.? ~ wrapBrackets(fieldDefinition.repSep0(whitespaceWithComment)).backtrack.?)).map {
      case (name, (directives, fields)) =>
        InterfaceTypeExtension(name, directives.getOrElse(Nil), fields.getOrElse(Nil))
    }


  private def interfaceTypeExtension: P[InterfaceTypeExtension] =
    P.defer(
      wrapWhitespaces(P.string("extend interface")).backtrack *> interfaceTypeExtensionWithOptionalDirectivesAndFields
    )

  private def unionTypeExtensionWithOptionalDirectivesAndUnionMembers: P[UnionTypeExtension] =
    (name.backtrack ~ (directives.backtrack.? <* wrapWhitespaces(P.char('=')).backtrack.?) ~ (wrapWhitespaces(P.char('|')).backtrack.? *> namedType.backtrack.?) ~ (wrapWhitespaces(P.char('|')).backtrack *> namedType).rep0).map {
      case (((name, directives), m), ms) =>
        UnionTypeExtension(name, directives.getOrElse(Nil), m.map(_ :: ms).getOrElse(ms).map(_.name))
    }

  private def unionTypeExtension: P[UnionTypeExtension] =
    P.defer(wrapWhitespaces(P.string("extend union")).backtrack *> unionTypeExtensionWithOptionalDirectivesAndUnionMembers)

  private def enumTypeExtensionWithOptionalDirectivesAndValues: P[EnumTypeExtension] =
    P.defer(enumName ~ directives.?.backtrack ~ wrapBrackets(enumValueDefinition.repSep0(whitespaceWithComment)).backtrack.?).map {
      case ((name, directives), enumValuesDefinition) =>
        EnumTypeExtension(name, directives.getOrElse(Nil), enumValuesDefinition.getOrElse(Nil))
    }

  private def enumTypeExtension: P[EnumTypeExtension] =
    P.defer(wrapWhitespaces(P.string("extend enum")).backtrack *> enumTypeExtensionWithOptionalDirectivesAndValues)

  private def inputObjectTypeExtensionWithOptionalDirectivesAndFields: P[InputObjectTypeExtension] =
    P.defer(name ~ directives.backtrack.? ~ wrapBrackets(argumentDefinition.rep0).backtrack.?).map {
      case ((name, directives), fields) =>
        InputObjectTypeExtension(name, directives.getOrElse(Nil), fields.getOrElse(Nil))
    }

  private def inputObjectTypeExtension: P[InputObjectTypeExtension] =
    P.defer(
      wrapWhitespaces(P.string("extend input")).backtrack *> (
        inputObjectTypeExtensionWithOptionalDirectivesAndFields
          //orElse inputObjectTypeExtensionWithDirectives
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
    P.defer(operationDefinition | fragmentDefinition)

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

  def document: P[ParsedDocument] =
    P.defer((P.start.with1 *> definition.rep) <* P.end).map(seq => ParsedDocument(seq.toList))

  /**
   * Parses the given string into a [[caliban.parsing.adt.Document]] object or fails with a [[caliban.CalibanError.ParsingError]].
   */
  def parseQuery(query: String): IO[ParsingError, Document] = {
    val sm = SourceMapper(query)
    document.parse(query) match {
      case Left(error) =>
        IO.fail(ParsingError(error.toString, Some(sm.getLocation(error.failedAtOffset))))
      case Right(result) =>
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
