#lang racket/base

(require racket/generic)
(require racket/string)
(require racket/list)
(require racket/port)


(define FileType-Default "GOLD Parser Tables/v1.0")

; NACHRICHTENKONSTANTEN, DIE DER PARSER AN DEN DRIVER ZURÜCKGIBT
(define ActionConstants.actionShift 1) ;Shift a symbol and goto a state
(define ActionConstants.actionReduce 2) ; Reduce by a specified rule
(define ActionConstants.actionGoto 3) ; Goto to a state on reduction
(define ActionConstants.actionAccept 4) ; Input successfully parsed
(define ActionConstants.actionError 5) ; Programmars see this often!

; KONSTANTEN ZUR VERARBEITUNG VON CGT DATEIEN	
(define EntryContentConstants.entryContentEmpty 69) ; Defined as E
(define EntryContentConstants.entryContentInteger 73) ; Defined as I - Signed, 2 byte
(define EntryContentConstants.entryContentString 83) ; Defined as S - Unicode format
(define EntryContentConstants.entryContentBoolean 66) ; Defined as B - 1 byte, Value is 0 or 1
(define EntryContentConstants.entryContentByte 98) ; Defined as b

; NACHRICHTENKONSTANTEN, DIE DER GOLD-PARSER AN DEN BENUTZER GIBT
(define GPMessageConstants.gpMsgTokenRead 201) ; A new token is read
(define GPMessageConstants.gpMsgReduction 202) ; A rule is reduced
(define GPMessageConstants.gpMsgAccept 203) ; Grammar complete 
(define GPMessageConstants.gpMsgNotLoadedError 204) ; No grammar is loaded
(define GPMessageConstants.gpMsgLexicalError 205) ; Token not recognized 
(define GPMessageConstants.gpMsgSyntaxError 206) ; Token is not expected
(define GPMessageConstants.gpMsgCommentError 207) ; Reached the end of the file - mostly due to being stuck in comment mode
(define GPMessageConstants.gpMsgInternalError 208); Something is wrong, very wrong
(define GPMessageConstants.gpMsgShift 209) ; A token is shifted
(define GPMessageConstants.gpMsgReductionTrimmed 210) ; A rule is reduced and trimmed

; KONSTANTEN FÜR DIE NACHRICHTEN, DIE DER PARSER GIBT
(define ParseResultConstants.parseResultAccept 301)
(define ParseResultConstants.parseResultShift 302)
(define ParseResultConstants.parseResultReduceNormal 303)
(define ParseResultConstants.parseResultReduceEliminated 304)
(define ParseResultConstants.parseResultSyntaxError 305)
(define ParseResultConstants.parseResultInternalError 306)

; KONSTANTEN FÜR DIE VERARBEITUNG VON CGT DATEIEN
(define RecordIDConstants.recordIdParameters 80) ; Defined as P
(define RecordIDConstants.recordIdTableCounts 84) ; Defined as T
(define RecordIDConstants.recordIdInitial 73) ; Defined as I
(define RecordIDConstants.recordIdSymbols 83) ; Defined as S
(define RecordIDConstants.recordIdCharSets 67) ; Defined as C
(define RecordIDConstants.recordIdRules 82) ; Defined as R
(define RecordIDConstants.recordIdDFAStates 68) ; Defined as D
(define RecordIDConstants.recordIdLRTables 76) ; Defined as L
(define RecordIDConstants.recordIdComment 33) ; Defined as !

; KONSTANTEN FÜR DIE AUSZEICHNUNG VON SYMBOLEN
(define SymbolTypeConstants.symbolTypeNonterminal 0) ; Normal nonterminal
(define SymbolTypeConstants.symbolTypeTerminal 1) ; Normal terminal
(define SymbolTypeConstants.symbolTypeWhitespace 2) ; Type of terminal
(define SymbolTypeConstants.symbolTypeEnd 3) ; End character (EOF)
(define SymbolTypeConstants.symbolTypeCommentStart 4) ; Comment start
(define SymbolTypeConstants.symbolTypeCommentEnd 5) ; Comment end
(define SymbolTypeConstants.symbolTypeCommentLine 6) ; Comment line
(define SymbolTypeConstants.symbolTypeError 7) ; Error symbol

; KLASSE ZUR REPRÄSENTATION EINER KANTE IN EINEM GRAPHEN EINES DFA
(struct FAEdge (chars targetIndex) #:mutable #:transparent)

; Returns True if the characters are in the String passed in, false if not.
(define (FAEdge.contains faedge what)
  (string-contains? (FAEdge-chars faedge) what))

; KLASSE ZUR REPRÄSENTATION EINES ZUSTANDES IN EINEM DFA
(struct FAState (edges acceptSymbol) #:mutable #:transparent)

; returns true, if there is an edge with target 
(define (FAState.edges.containsTargetIndex edges idx)
  (if (not (index-where edges (lambda (e) (eq? (FAEdge-targetIndex e) idx))))
      #f
      #t
      ))

; finds the edge with target and appends the chars to its chars
(define (FAState.edges.appendChars fastate chars target)
  (let* ([idx (index-where (FAState-edges fastate) (lambda (e) (eq? (FAEdge-targetIndex e) target)))]
         [edge (list-ref (FAState-edges fastate) idx)]
         [chrs (string-append (FAEdge-chars edge) chars)])
    (set-FAState-edges! fastate (list-set (FAState-edges) idx (FAEdge chrs (FAEdge-targetIndex edge))))
    ))

; This method will add an edge to the FAState. It will create a new edge if there are no chars (the lambda edge), otherwise
; it will find the index from the target passed in, and create a new edge with the target index of the target passed in, and
; the characters passed in. If the target is not found, it will produce an error.
(define (FAState.addEdge fastate chars target)
  (if (eq? chars "")
      (set-FAState-edges! fastate (append (FAState-edges fastate) (list (FAEdge chars target))))
      (if (FAState.edges.containsTargetIndex (FAState-edges fastate) target)
          (FAState.edges.appendChars fastate chars target)
          (set-FAState-edges! fastate (append (FAState-edges fastate) (list (FAEdge chars target))))
          )
      ))

; This method will return the edge at the specified index for this state.
(define (FAState.edge fastate index)  
  (if (and (>= index 0) (< index (FAState.edgeCount fastate)))
      (list-ref (FAState-edges fastate) index)
      (void)))
  

; The number of edges in this FAState.
(define (FAState.edgeCount fastate)
  (length (FAState-edges fastate)))

; EINE VARIABLE EINER VON GOLD ERSTELLTEN GRAMMATIK
(struct VariableType (name visible value comment) #:mutable #:transparent)

; BEHÄLTER FÜR VARIABLEN DER GRAMMATIKEN DIE VON GOLD ERSTELLT WERDEN
(struct VariableList (memberList memberCount) #:mutable #:transparent)

; This method will add a new variable to the list. It will do this if and only if there is not an equivalent variable already in
; the list. If there is not, it will create a new VariableType
(define (VariableList.add variableList name value comment)
  (let ([c (VariableList-memberCount variableList)])
    (if (= 0 c)
        (begin
          (set-VariableList-memberList! variableList (list (VariableType name #t value comment)))
          (set-VariableList-memberCount! variableList 1)
          #t
          )
        (let ([i (index-where variableList (lambda (v) (eq? (VariableType-name v) name)))])
          (if (number? i)
              #f
              (let ([ml (append (VariableList-memberList variableList) (list (VariableType name #t value comment)))]
                    [mc (add1 (VariableList-memberCount variableList))])
                (begin
                  (set-VariableList-memberList! variableList ml)
                  (set-VariableList-memberCount! variableList mc)
                  #t
                  )
                )
              )))
    ))

; This method will set the name of each variable to ""
(define (VariableList.clearValues variableList)
  (begin
    (set-VariableList-memberList!
     variableList
     (map (lambda (v)
            ((set-VariableType-name! v  "")
             ))
          (VariableList-memberList variableList)))
    (set-VariableList-memberCount! variableList 0)
    )
  )

; Return the name of the Variable at the specified index. It will do this if and only if the index is not less than 0, and if
; the index is less than the current number of variables.
(define (VariableList.name variableList index)
  (if (and (>= index 0) (< index (VariableList-memberCount variableList) ))
      (VariableType-name (list-ref (VariableList-memberList index)))
      void
      ))

; This method sets the value of a variable of the same name as that specified.
(define (VariableList.setValue variableList name value)
  (let ([i (VariableList.variableIndex variableList name)])
    (if (> i -1)
        (set-VariableType-value! (list-ref (VariableList-memberList variableList) i) value)
        void
        )))

; This method will return the value of the variable with the same name as that specified.
(define (VariableList.getValue variableList name)
  (let ([i (VariableList.variableIndex variableList name)])
    (if (> i -1)
        (VariableType-value (list-ref (VariableList-memberList variableList) i))
        void
        )))

; This method will return the index number of a variable that has the same name as that specified.
(define (VariableList.variableIndex variableList name)
  (let ([i (index-where (VariableList-memberList variableList)
                        (lambda (v)
                          (eq? (VariableType-name  v) name)))])
    (if (number? i)
        i
        -1
        )))

; KLASSE FÜR DIE BEZEICHNUNG EINES SYMBOLS EINER GEPARSTEN SPRACHE
(struct Symbol (name pattern kind variableLength tableIndex) #:mutable #:transparent)

; This method will create a text representation of this Symbol. What text is returned depends on the kind of Symbol.
; If it is a Non-Terminal, angular brackets are placed before and after, if it is a Terminal, then it is formatted.
; Everything else is placed in parenthesis.
(define (Symbol.getText symbol)
  (cond
    [(eq? (Symbol-kind symbol) SymbolTypeConstants.symbolTypeNonterminal )
     (format "<~s>" (Symbol-name symbol))
     ]
    [(eq? (Symbol-kind symbol) SymbolTypeConstants.symbolTypeTerminal)
     (_Symbol.patternFormat (Symbol-name symbol))
     ]
    [else
     (format "(~s)" (Symbol-name symbol))
     ]
    ))

; this method is not accessible. It will create a formatted String from that passed in.
(define (_Symbol.patternFormat name)
  (let ([stringList (string->list name)]
        [ch34 (integer->char 34)])
    (list->string (flatten (map (lambda (c)
                                  (if (string=? (format "~c" c) "'")
                                      (string->list "''")
                                      (if (or (string-contains? "|-+*?()[]{}<>!" (format "~c" c)) (eq? c ch34))
                                          (string->list (format "'~c'" c))
                                          c
                                          )
                                      )) stringList)))
    ))

; This method will check equality of two Symbols - this and the one passed in.
(define (Symbol.isEqual symbol other)
  (and (string=? (Symbol-name symbol) (Symbol-name other))
       (eq? (Symbol-kind symbol) (Symbol-kind other))
       ))

; EIN OBJEKT FÜR DIE SPEICHERUNG VON DATEN FÜR DIE WEITERVERARBEITUNG IN EINEM PARSER	
(struct Token (state data parentSymbol) #:mutable #:transparent)

; This method will get the name of this Token. This is the name of the parent symbol in the getName() method.
(define (Token.name token)
  (Symbol-name (Token-parentSymbol token)
               ))

; This method will get the text of this Token. This is the text in the parent symbol getText() method.
(define (Token.text token)
  (Symbol.getText (Token-parentSymbol token)
                  ))

; This method will get the table index of this Token.
(define (Token.tableIndex token)
  (Symbol-tableIndex (Token-parentSymbol token)
                     ))

; This method will get the kind of this Token. This is contained in the parent symbol, and defined in SymbolTypeConstants.
(define (Token.kind token)
  (Symbol-kind (Token-parentSymbol token)))


; BEHÄLTER FÜR DIE AUS EINER GOLD GRAMMATIK GENERIERTE SYMBOLTABELLE
(struct SymbolList (memberList memberCount) #:mutable #:transparent)

; This method empties the list.
(define (SymbolList.clear symbolList)
  (begin
    (set-SymbolList-memberList! symbolList '())
    (set-SymbolList-memberCount! symbolList 0)
    ))

; Weiche zwischen den Funktionen getMemberByIndex und getMemberByName
(define (SymbolList.getMember symbolList var)
  (begin ;(newline) (newline)(display "getMember")(newline)(display symbolList) (newline) (display var) (newline)
    (cond [(number? var) (SymbolList.getMemberByIndex symbolList var)]
          [(string? var) (SymbolList.getMemberByName symbolList var)]
          )))

; This method will return the Symbol at the specified index. It will do this if and only if the index is not less than 0, and
; if the index is less than the current number of symbols.
(define (SymbolList.getMemberByIndex symbolList index)
  (if (and (>= index 0) (< index (SymbolList-memberCount symbolList)))
      (list-ref (SymbolList-memberList symbolList) index)
      (void)
      ))

; This method will return the Symbol that has an equivalent name in the list.
(define (SymbolList.getMemberByName symbolList name)
  (let ([ idx (index-where (SymbolList-memberList symbolList)
                           (lambda (x)
                             (eq? (Symbol-name x) name)
                             ))])
    (if (number? idx)
        (list-ref (SymbolList-memberList symbolList) idx)
        void)
    ))

;  This method will set the element at the specified index to the Symbol passed in. It will do this if and only if
; the index is not less than 0, and if the index is less than the current member count.
(define (SymbolList.setMember symbolList index symbol)
  (if (and (>= index 0) (< index (SymbolList-memberCount symbolList)))
      (set-SymbolList-memberList! symbolList (list-set (SymbolList-memberList symbolList) index symbol))
      (void)
      ))

; This method adds a symbol to the end of the list.
(define (SymbolList.add symbolList newItem)
  (begin
    (set-SymbolList-memberCount! symbolList (add1 (SymbolList-memberCount symbolList)))
    (set-SymbolList-memberList! symbolList (append (SymbolList-memberList symbolList) (list newItem)))
    (- (SymbolList-memberCount symbolList) 1)
    ))

; KLASSE FÜR DIE VERARBEITUNG VON CGT DATEIEN
(struct SimpleDatabase ([database #:auto] [bFileOpen #:auto] [fileNumber #:auto] [buff #:auto] [buffPort #:auto]
                                          [fileType #:auto] [entryReadPosition #:auto] [entryList #:auto]) #:mutable #:transparent)

; This method will open the file for reading.
(define (SimpleDatabase.openFile simpleDatabase filename)
  (letrec ([f (open-input-file filename #:mode 'binary)]
           [b (port->bytes f)]
           )
    (begin
      (set-SimpleDatabase-database! simpleDatabase f)
      (set-SimpleDatabase-bFileOpen! simpleDatabase #t)
      (set-SimpleDatabase-fileNumber! simpleDatabase 0)
      (set-SimpleDatabase-buff! simpleDatabase b)
      (set-SimpleDatabase-buffPort! simpleDatabase (open-input-bytes b))
      (set-SimpleDatabase-entryReadPosition! simpleDatabase 0)
      (set-SimpleDatabase-entryList! simpleDatabase (list))
      (_SimpleDatabase.hasValidHeader simpleDatabase)
      )
    ))

; this method will close the file and set the Buffer to null.
(define (SimpleDatabase.closeFile simpleDatabase)
  (begin
    (set-SimpleDatabase-buff! simpleDatabase '())
    (close-input-port (SimpleDatabase-buffPort simpleDatabase))
    (close-input-port (SimpleDatabase-database simpleDatabase))
    #t
    ))

; This method will retrieve a set of integers that have been read by the SimpleDatabase file.
(define (SimpleDatabase.retrieve simpleDatabase numParams)
  (let ([currentEntry (list-ref (SimpleDatabase-entryList simpleDatabase) (SimpleDatabase-entryReadPosition simpleDatabase))])
    (if (= 0 (- numParams 1))
        currentEntry
        (begin
          (set-SimpleDatabase-entryReadPosition! simpleDatabase (add1 (SimpleDatabase-entryReadPosition simpleDatabase)))
          (cons currentEntry (SimpleDatabase.retrieve simpleDatabase (- numParams 1)))
          ))
    ))

; This method checks to see if there no many fields or records to be read.
(define (SimpleDatabase.retrieveDone simpleDatabase)
  (not (< (SimpleDatabase-entryReadPosition simpleDatabase) (length (SimpleDatabase-entryList simpleDatabase)))
       ))

; This method will retrieve an Object that has been read in by the SimpleDatabase. It could be a String, Boolean etc.
(define (SimpleDatabase.retrieveNext simpleDatabase)
  (if (not (SimpleDatabase.retrieveDone simpleDatabase))
      (let ([currentEntry (list-ref (SimpleDatabase-entryList simpleDatabase) (SimpleDatabase-entryReadPosition simpleDatabase))])
        (begin
          (set-SimpleDatabase-entryReadPosition! simpleDatabase (add1 (SimpleDatabase-entryReadPosition simpleDatabase)))
          currentEntry
          ))
      '()
      ))

; reads two bytes until two consecutive 0 are encountered
(define (Read-String-Bytes-From-Buffer buf-port)
  (let ([b1 (read-byte buf-port)]
        [b2 (read-byte buf-port)])
    (if (and (= 0 b1) (= 0 b2))
        '()
        (if (= 0 b1)
            (cons b2 (Read-String-Bytes-From-Buffer buf-port))
            (cons b1 (Read-String-Bytes-From-Buffer buf-port))))
    ))

; reads a unicode string from the database
(define (Read-String-From-Buffer buf-port)
  (let ([string-bytes (Read-String-Bytes-From-Buffer buf-port)])
    (bytes->string/latin-1 (list->bytes string-bytes))
    ))

; reads bytes until a non-zero value is encountered
(define (Read-Until-Next-Nonzero buf-port)
  (let ([b (read-byte buf-port)])
    (if (not (= b 0))
        b
        (Read-Until-Next-Nonzero buf-port)
        )))

; this method is inaccessible. It will check the file header of the file opened, and return true if it agrees with the file
; type already set up, false if not.
(define (_SimpleDatabase.hasValidHeader simpleDatabase)
  (letrec ([ft (SimpleDatabase-fileType simpleDatabase)]
           [h (Read-String-From-Buffer (SimpleDatabase-buffPort simpleDatabase))])
    (string=? h ft)
    ))

; This method will check to see if we have reached the end of the file.
(define (SimpleDatabase.done simpleDatabase)
  (if (SimpleDatabase-bFileOpen simpleDatabase)
      (> (file-position (SimpleDatabase-buffPort simpleDatabase)) (- (bytes-length (SimpleDatabase-buff simpleDatabase)) 2) )
      #t
      ))

; This method will read the file for the next record, and place each field in the Vector to be retrieved later.
(define (SimpleDatabase.getNextRecord simpleDatabase)
  (let ([recordID (Read-Until-Next-Nonzero (SimpleDatabase-buffPort simpleDatabase))])
    (begin
      (SimpleDatabase.clear simpleDatabase)
      (if (= recordID 77)
          (letrec ([b (read-bytes  2 (SimpleDatabase-buffPort simpleDatabase))]
                   [cnt (integer-bytes->integer b #f)])
            (begin
              
              (for ([i (range cnt)])
                (_SimpleDatabase.readEntry simpleDatabase))
              (set-SimpleDatabase-entryReadPosition! simpleDatabase 0)
              #t
              ))
          #f
          ))
    ))

; this method is inaccesible. It will read a portion of the database file and create a new Object or an integer depending
; on what the next field is, which is identified by the number of the byte - which itself is given in the EntryContentConstants
; interface. Please do NOT edit this method! Nasty things will happen.
(define (_SimpleDatabase.readEntry simpleDatabase)
  (let ([b0 (Read-Until-Next-Nonzero (SimpleDatabase-buffPort simpleDatabase))])
    (cond [(= b0 EntryContentConstants.entryContentEmpty)
           (set-SimpleDatabase-entryList! simpleDatabase (append (SimpleDatabase-entryList simpleDatabase) (list "")))]
          [(= b0 EntryContentConstants.entryContentInteger)
           (letrec ([b (read-bytes 2 (SimpleDatabase-buffPort simpleDatabase))]
                    [i (integer-bytes->integer b #f)])
             (set-SimpleDatabase-entryList! simpleDatabase (append (SimpleDatabase-entryList simpleDatabase) (list i))))]
          [(= b0 EntryContentConstants.entryContentString)
           (let ([s (Read-String-From-Buffer (SimpleDatabase-buffPort simpleDatabase))])
             (set-SimpleDatabase-entryList! simpleDatabase (append (SimpleDatabase-entryList simpleDatabase) (list s))))
           ]
          [(= b0 EntryContentConstants.entryContentBoolean)
           (let ([b1 (read-byte (SimpleDatabase-buffPort simpleDatabase))])
             (if (= b1 1)
                 (set-SimpleDatabase-entryList! simpleDatabase (append (SimpleDatabase-entryList simpleDatabase) (list #t)))
                 (set-SimpleDatabase-entryList! simpleDatabase (append (SimpleDatabase-entryList simpleDatabase) (list #f)))
                 ))]
          [(= b0 EntryContentConstants.entryContentByte)
           (set-SimpleDatabase-entryList! simpleDatabase
                                          (append (SimpleDatabase-entryList simpleDatabase)
                                                  (list (read-byte (SimpleDatabase-buffPort simpleDatabase)))))]
          )))

; This method will reset all the currently read fields.
(define (SimpleDatabase.clear simpleDatabase)
  (begin
    (set-SimpleDatabase-entryReadPosition! simpleDatabase 0)
    (set-SimpleDatabase-entryList! simpleDatabase '())
    ))

; KLASSE FÜR DIE REPRÄSENTATION VON REGELN IN EINER GOLD GRAMMATIK
(struct Rule (pRuleNonTerminal pRuleSymbols pTableIndex) #:mutable #:transparent)

; Will return how many symbols are contained in this Rule.
(define (Rule.getSymbolCount rule)
  (SymbolList-memberCount (Rule-pRuleSymbols rule))
  )

; fetches the rule at the specified index
(define (Rule.getSymbols rule index)
  (if (and (>= index 0) (< index (Rule.getSymbolCount rule)))
      (SymbolList.getMember (Rule-pRuleSymbols rule) index)
      void
      ))

; Will return a String consisting of the Rules name. This is in the format < 'name of non-terminal' >
(define (Rule.name rule)
  (format "<~s>" (Symbol-name (Rule-pRuleNonTerminal rule))
          ))

; This method will return the right hand side of the rule, It does this by concatenating all the Symbols in the Symbol list.
(define (Rule.definition rule)
  (string-join (map Symbol.getText (SymbolList-memberList (Rule-pRuleSymbols rule)))
               ))

; fügt der Symbolliste ein neues Element hinzu
(define (Rule.addItem rule item)
  (SymbolList.add (Rule-pRuleSymbols rule) item))

; This method uses the method name() and definiton() to create a String representing the entirety of this Rule.
(define (Rule.getText rule)
  (string-append (list (Rule.name rule) " ::= " (Rule.definition rule))
                 ))

; This method will check to see if the rule contains a non terminal.
(define (Rule.containsOneNonTerminal rule)
  (if (= 1 (Rule.getSymbolCount rule))
      (if (= (Symbol-kind (SymbolList.getMember (Rule-pRuleSymbols rule) 0)) SymbolTypeConstants.symbolTypeNonterminal)
          #t
          #f)
      #f
      ))

; This method will check equality of two Rules - this and the one passed in.
(define (Rule.isEqual rule otherRule)
  (if (= (SymbolList-memberCount (Rule-pRuleSymbols rule)) (SymbolList-memberCount (Rule-pRuleSymbols otherRule)))
      (if (Symbol.isEqual (Rule-pRuleNonTerminal rule) (Rule-pRuleNonTerminal otherRule))
          (andmap Symbol.isEqual (SymbolList-memberList (Rule-pRuleSymbols rule))
                  (SymbolList-memberList (Rule-pRuleSymbols otherRule)))
          #f)
      #f  
      ))

; KLASSE FÜR DIE REPRÄSENTATION EINER VON EINEM PARSER VORGENOMMENE REDUKTION															*
(struct Reduction (pTokens pTokenCount parentRule pTag) #:mutable #:transparent)

; This method implicitly sets the number of tokens in this Reduction. If the value is 0 or less, then we clear the tokens
; in this reduction and set the number of tokens to 0.
(define (Reduction.setTokenCount reduction count)
  (if (< count 1)
      (begin
        (set-Reduction-pTokens! reduction '())
        (set-Reduction-pTokenCount! reduction 0)
        )
      (begin
        (set-Reduction-pTokenCount! reduction count)
        (set-Reduction-pTokens! reduction (make-list count #f))
        )
      ))

; Will retrieve a Token at the specified index. The index specified must be equal or greater than 0 and less than
; the current number of Tokens.
(define (Reduction.getToken reduction index)
  (if (and (>= index 0) (< index (Reduction-pTokenCount reduction)))
      (list-ref (Reduction-pTokens reduction) index)
      void
      ))

; Will place a Token at the specified index. It will only do this if the index is greater or equal to 0, and less than the
; token count
(define (Reduction.setToken reduction index value)
  (if (and (>= index 0) (< index (Reduction-pTokenCount reduction)))
      (set-Reduction-pTokens! reduction (list-set (Reduction-pTokens reduction) index value))
      void
      ))

; KLASSE FÜR DIE REPRÄSENTATION EINER LALR AKTION
(struct LRAction (pSymbol actionConstant value) #:mutable #:transparent)

; This method will return the index of the smybol in the symbol table.
(define (LRAction.getSymbolIndex lraction)
  (Symbol-tableIndex (LRAction-pSymbol lraction)
                     ))

; KLASSE FÜR DIE BEHANDLUNG EINER LALR TABELLE
(struct LRActionTable (memberList memberCount) #:mutable #:transparent)

;  This method will return the index in the symbol table for the symbol in the action table specified by symbolIndex
(define (LRActionTable.actionIndexForSymbol lractionTable symbolIndex)
  (let ([n (for/or ([i (range 0 (- (length (LRActionTable-memberList lractionTable)) 0))])
             (let ([lar (list-ref (LRActionTable-memberList lractionTable) i)])
               (if (= (Symbol-tableIndex (LRAction-pSymbol lar)) symbolIndex)
                   i
                   #f
                   ))
             )])
    (if (number? n) n -1)))

; This method will add a symbol to the action table. It will create a new LRAction, set its value and actionConstant,
; and then increment the member count after adding it.
(define (LRActionTable.addItem lractionTable sym actionConstant value)
  (begin
    (set-LRActionTable-memberCount! lractionTable (add1 (LRActionTable-memberCount lractionTable)))
    (set-LRActionTable-memberList! lractionTable (append (LRActionTable-memberList lractionTable)
                                                         (list (LRAction sym actionConstant value))))
    ))

;This method will return the LRAction at the specified index. It will only return if and only if the index is a valid number.
(define (LRActionTable.item lractionTable itemIndex)
  (if (and (>= itemIndex 0) (< itemIndex (LRActionTable-memberCount lractionTable)))
      (list-ref (LRActionTable-memberList lractionTable) itemIndex)
      void
      ))

; LALR-PARSER FÜR KONTEXTFREIE GRAMMATIKEN
(struct GOLDParser (pSymbolTable pDFA pCharacterSetTable pRuleTable pVariables pActionTable kErrorSymbol
                                 kEndSymbol initialDFAState startSymbol initialLALRState currentLALR
                                 stack pTokens pHaveReductions pTrimReductions pTablesLoaded
                                 pLineNumber pCharacterPos pSource pCommentLevel pInputTokens
                                 pIgnoreCase) #:mutable #:transparent)

; initializes the parser
(define (GOLDParser.prepareToParse parser)
  (set-GOLDParser-stack! parser (append
                                 (GOLDParser-stack parser)
                                 (list (Token (GOLDParser-initialLALRState parser) ""
                                              (SymbolList.getMember (GOLDParser-pSymbolTable parser)
                                                                    (GOLDParser-startSymbol parser)))))
                         ))

; This method will close the source file.
(define (GOLDParser.closeFile parser)
  (close-input-port (GOLDParser-pSource parser)
                    ))

; This method returns the current Token. The current token is the last token read by "retrieveToken".
(define (GOLDParser.currentToken parser)
  (last (GOLDParser-pInputTokens parser)
        ))

; This method should only be called if there is a lexical error and you need to pop an unexpected token out of the stack.
(define (GOLDParser.popInputToken parser)
  (set-GOLDParser-pInputTokens! parser (take (GOLDParser-pInputTokens parser) (- (length GOLDParser-pInputTokens parser) 1))
                                ))

; This method should only be used if there is a syntax error. It will push a Token onto the top of the stack so that the
; parser might have a chance of finding an correctly typed token.
(define (GOLDParser.pushInputToken parser token)
  (set-GOLDParser-pInputTokens! parser (append (GOLDParser-pInputTokens parser) (list token))
                                ))

; If you require access to tokens in the stack before they are placed on the parse tree. Enter an index number
; and the Token will be returned, if and only if the index number is valid.
(define (GOLDParser.getToken parser index)
  (if (and (> index 0) (< index (length (GOLDParser-pTokens parser))))
      (list-ref (GOLDParser-pTokens parser) index)
      void
      ))

; This method will return the current reduction. This will only happen if the parsing engine has performed a reduction. If it
; has, then the reduction passed back will be the last one performed.
(define (GOLDParser.currentReduction parser)
  (if (GOLDParser-pHaveReductions parser)
      (Token-data (last (GOLDParser-stack parser)))
      void
      ))

; This method will set the current reduction to the one passed in.
(define (GOLDParser.setCurrentReduction parser value)
  (if (GOLDParser-pHaveReductions parser)
      (set-GOLDParser-stack!
       parser
       (list-update
        (GOLDParser-stack parser)
        (- (length GOLDParser-stack) 1)
        (lambda (x) (set-Token-data! x value))))
      void
      ))

; this method is not accessible. It will read until a line break is found and simply discard it.
(define (_GOLDParser.discardRestOfLine parser)
  (read-line (GOLDParser-pSource parser) 'any
             ))

; This method will return the value of a parameter that corresponds to the name passed in.
(define (GOLDParser.parameter parser name)
  (hash-ref (GOLDParser-pVariables parser) name
            ))

; This method returns the total number of symbols in the symbol table.
(define (GOLDParser.symbolTableCount parser)
  (SymbolList-memberCount (GOLDParser-pSymbolTable parser)
                          ))

; This method returns the total number of rules in the rule table.
(define (GOLDParser.ruleTableCount parser)
  (length (GOLDParser-pRuleTable parser)
          ))

; This method will return a Symbol at the specified index.
(define (GOLDParser.symbolTableEntry parser index)
  (SymbolList.getMember (GOLDParser-pSymbolTable parser) index
                        ))

; This method will return a Rule at the specified index.
(define (GOLDParser.ruleTableEntry parser index)
  (if (and (> index 0) (< index (length (GOLDParser-pRuleTable parser))))
      (list-ref (GOLDParser-pRuleTable parser) index)
      void
      ))

; This method will return the number of tokens in the stack.
(define (GOLDParser.tokenCount parser)
  (length (GOLDParser-pTokens parser)
          ))

; this method is not accessible. It will load all the information contained in the .cgt file passed in
; as the fileName parameter. It will then store this information in the relevant tables
; and storage defined as class variables in this class.
(define (_GOLDParser.loadTables parser fileName)
  (let ([db (SimpleDatabase)])
    (begin
      (set-SimpleDatabase-fileType! db FileType-Default)
      (if (SimpleDatabase.openFile db fileName)
          (begin
            (do ([success #t])
              ((or (SimpleDatabase.done db) (not success)))
              (if (SimpleDatabase.getNextRecord db)
                  (let ([next (SimpleDatabase.retrieveNext db)])
                    (cond
                      [(= next RecordIDConstants.recordIdParameters)
                       (begin
                         (set-GOLDParser-pVariables! parser (hash-set (GOLDParser-pVariables parser) "Name" (SimpleDatabase.retrieveNext db)))
                         (set-GOLDParser-pVariables! parser (hash-set (GOLDParser-pVariables parser) "Version" (SimpleDatabase.retrieveNext db)))
                         (set-GOLDParser-pVariables! parser (hash-set (GOLDParser-pVariables parser) "Author" (SimpleDatabase.retrieveNext db)))
                         (set-GOLDParser-pVariables! parser (hash-set (GOLDParser-pVariables parser) "About" (SimpleDatabase.retrieveNext db)))
                         (set-GOLDParser-pVariables! parser (hash-set (GOLDParser-pVariables parser) "Case Sensitive" (SimpleDatabase.retrieveNext db)))
                         (set-GOLDParser-pVariables! parser (hash-set (GOLDParser-pVariables parser) "Start Symbol" (SimpleDatabase.retrieveNext db)))
                         )
                       ]
                      [(= next RecordIDConstants.recordIdTableCounts)
                       (begin
                         (set-SymbolList-memberCount! (GOLDParser-pSymbolTable parser) (SimpleDatabase.retrieveNext db))
                         (set-SymbolList-memberList! (GOLDParser-pSymbolTable parser) (make-list (SymbolList-memberCount (GOLDParser-pSymbolTable parser)) 0))
                         (set-GOLDParser-pCharacterSetTable! parser
                                                             (make-list (SimpleDatabase.retrieveNext db) #f))
                         (set-GOLDParser-pRuleTable! parser (make-list (SimpleDatabase.retrieveNext db) #f))
                         (set-GOLDParser-pDFA! parser (make-list (SimpleDatabase.retrieveNext db) #f))
                         (set-GOLDParser-pActionTable! parser (make-list (SimpleDatabase.retrieveNext db) #f))
                         )
                       ]
                      [(= next RecordIDConstants.recordIdInitial)
                       (let ([data (SimpleDatabase.retrieve db 2)])
                         (begin
                           (set-GOLDParser-initialDFAState! parser (car data))
                           (set-GOLDParser-initialLALRState! parser (cdr data))
                           )
                         )
                       ]
                      [(= next RecordIDConstants.recordIdSymbols)
                       (let ([tableIndex (SimpleDatabase.retrieveNext db)]
                             [name (SimpleDatabase.retrieveNext db)]
                             [kind (SimpleDatabase.retrieveNext db)]
                             [empty (SimpleDatabase.retrieveNext db)]
                             )
                         (let ([sym (Symbol name "" kind -1 tableIndex)]
                               [symList (GOLDParser-pSymbolTable parser)]
                               [p parser])
                           (SymbolList.setMember (GOLDParser-pSymbolTable parser) tableIndex sym)
                           )
                         )
                       ]
                      [(= next RecordIDConstants.recordIdCharSets)
                       (set-GOLDParser-pCharacterSetTable!
                        parser
                        (list-set
                         (GOLDParser-pCharacterSetTable parser)
                         (SimpleDatabase.retrieveNext db)
                         (SimpleDatabase.retrieveNext db)))
                       ]
                      [(= next RecordIDConstants.recordIdRules)
                       (let ([idx (SimpleDatabase.retrieveNext db)]
                             [symbolIndex (SimpleDatabase.retrieveNext db)]
                             [reserved (SimpleDatabase.retrieveNext db)])
                         (let ([rule (Rule (SymbolList.getMember (GOLDParser-pSymbolTable parser) symbolIndex) (SymbolList '() 0) idx)])
                           (if (not (SimpleDatabase.retrieveDone db))
                               (begin (do ([dummy #f])
                                        ((SimpleDatabase.retrieveDone db))
                                        (let ([n (SimpleDatabase.retrieveNext db) ])
                                          (Rule.addItem rule (SymbolList.getMember (GOLDParser-pSymbolTable parser) n))
                                          )
                                        )
                                      )
                               (void)
                               )
                           (set-GOLDParser-pRuleTable! parser (list-set (GOLDParser-pRuleTable parser) idx rule))
                           )
                         )
                       ]
                      [(= next RecordIDConstants.recordIdDFAStates)
                       (begin
                         (let ([idx (SimpleDatabase.retrieveNext db)]
                               [accept (SimpleDatabase.retrieveNext db)]
                               [acceptSymbol (SimpleDatabase.retrieveNext db)])
                           (let ([dfa (FAState '() (if accept acceptSymbol -1))])
                             (begin
                               (SimpleDatabase.retrieveNext db)
                               (if (not (SimpleDatabase.retrieveDone db))
                                   (do ([done (SimpleDatabase.retrieveDone db)])
                                     ((SimpleDatabase.retrieveDone db))
                                     (FAState.addEdge dfa (SimpleDatabase.retrieveNext db) (SimpleDatabase.retrieveNext db))
                                     (SimpleDatabase.retrieveNext db)
                                     )
                                   (void))
                               (set-GOLDParser-pDFA! parser (list-set (GOLDParser-pDFA parser) idx dfa))
                               )
                             )
                           )
                         )
                       ]
                      [(= next RecordIDConstants.recordIdLRTables)
                       (let ([idx (SimpleDatabase.retrieveNext db)]
                             [reserved (SimpleDatabase.retrieveNext db)])
                         (let ([lr (LRActionTable '() 0)])
                           (begin
                             (do ([dummy #f])
                               ((SimpleDatabase.retrieveDone db))
                               (let ([sIndex (SimpleDatabase.retrieveNext db)]
                                     [action (SimpleDatabase.retrieveNext db)]
                                     [target (SimpleDatabase.retrieveNext db)]
                                     [reserved (SimpleDatabase.retrieveNext db)])
                                 (LRActionTable.addItem lr (SymbolList.getMember (GOLDParser-pSymbolTable parser) sIndex)
                                                        action target)
                                 ))
                             (set-GOLDParser-pActionTable! parser (list-set (GOLDParser-pActionTable parser) idx lr))
                             )
                           )
                         )
                       ]
                      [else (set! success #f)]
                      )
                    )
                  (set! success #f)
                  ))
            (if (hash-ref (GOLDParser-pVariables parser) "Case Sensitive")
                (set-GOLDParser-pIgnoreCase! parser #f)
                (set-GOLDParser-pIgnoreCase! parser #t))
            (SimpleDatabase.closeFile db)
            #t
            )
          #f
          )
      )
    ))

; This method will reset the GOLDParser engine before loading a new .cgt file into it.
(define (GOLDParser.loadCompiledGrammar parser fileName)
  (begin
    (GOLDParser.clear parser)
    (_GOLDParser.loadTables parser fileName)
    ))

; This method will open the source file for reading. It will also reset all information from previous source files.
(define (GOLDParser.openFile parser fileName)
  (begin
    (GOLDParser.reset parser)
    (set-GOLDParser-pSource! parser (open-input-file fileName #:mode 'binary))
    (GOLDParser.prepareToParse parser)
    #t
    ))

; Öffnet eine Datei in dem Sinne, dass der Eingabestrom bereit-gestellt wird und der Inhalt
; des Stroms dem Parameter $content entspricht 
(define (GOLDParser.openText parser content)
  (begin
    (GOLDParser.reset parser)
    (set-GOLDParser-pSource! parser (open-input-string content))
    (GOLDParser.prepareToParse parser)
    #t
    ))

; This method clears every value in the parser engine.
(define (GOLDParser.clear parser)
  (begin
    (set-GOLDParser-pSymbolTable! parser (SymbolList '() 0))
    (set-GOLDParser-pRuleTable! parser '())
    (set-GOLDParser-pCharacterSetTable! parser '())
    (set-GOLDParser-pVariables! parser #hash())
    (set-GOLDParser-pTokens! parser '())
    (set-GOLDParser-pInputTokens! parser '())
    ))

; This method will reset the parser engine. It initalises the Error and Type End symbols,
; and then clears all the stacks of any tokens.
(define (GOLDParser.reset parser)
  (begin
    ;(display (SymbolList-memberList (GOLDParser-pSymbolTable parser)))
    (set-GOLDParser-currentLALR! parser (GOLDParser-initialLALRState parser))
    (set-GOLDParser-pLineNumber! parser 1)
    (set-GOLDParser-pCharacterPos! parser 1)
    (set-GOLDParser-pCommentLevel! parser 0)
    (set-GOLDParser-pHaveReductions! parser #f)
    (set-GOLDParser-pTokens! parser '())
    (set-GOLDParser-pInputTokens! parser '())
    (set-GOLDParser-stack! parser '())
    (let ([t (Token void void void)])
      (set-Token-state! t (GOLDParser-initialLALRState parser))
      (set-Token-parentSymbol! t (SymbolList.getMember (GOLDParser-pSymbolTable parser) 0))
      (set-GOLDParser-stack! parser (append (GOLDParser-stack parser) (list t)))
      )
    (for ([i (range (- (SymbolList-memberCount (GOLDParser-pSymbolTable parser)) 0))])
      (let ([swKind (Symbol-kind (SymbolList.getMember (GOLDParser-pSymbolTable parser) i))])
        (cond
          [(= swKind SymbolTypeConstants.symbolTypeError)
           (set-GOLDParser-kErrorSymbol! parser (SymbolList.getMember (GOLDParser-pSymbolTable parser) i))]
          [(= swKind SymbolTypeConstants.symbolTypeEnd)
           (set-GOLDParser-kEndSymbol! parser (SymbolList.getMember (GOLDParser-pSymbolTable parser) i))]
          )
        )
      )
    ))

; Will parse a token.
; 1. If the tables are not setup then report GPM_NotLoadedError<br>
; 2. If parser is in comment mode then read tokens until a recognized one is found and report it<br>
; 3. Otherwise, parser normal<br>
;  	 a. If there are no tokens on the stack
;           1) Read one and trap error
;           2) End function with GPM_TokenRead
;       b. Otherwise, call ParseToken with the top of the stack.
;           1) If success, then Pop the value
;           2) Loop if the token was shifted (nothing to report)
(define (GOLDParser.parse parser)
  (let ([result 0] [done #f])
    (begin
      (if (or (< (length (GOLDParser-pActionTable parser)) 1) (< (length (GOLDParser-pDFA parser)) 1))
          (set! result GPMessageConstants.gpMsgNotLoadedError)
          (do ([dummy #f])
            ((eq? done #t))
            (if (= (length (GOLDParser-pInputTokens parser)) 0)
                (letrec ([readToken (_GOLDParser.retrieveToken parser (GOLDParser-pSource parser))])
                  
                  (if (eq? (Token-data readToken) void)
                      GPMessageConstants.gpMsgNotLoadedError
                      (if (not (eq? (Token.kind readToken) SymbolTypeConstants.symbolTypeWhitespace))
                          (begin
                            (set-GOLDParser-pInputTokens! parser (append (GOLDParser-pInputTokens parser) (list readToken)))
                            (if (and (= (GOLDParser-pCommentLevel parser) 0)
                                     (not (= (Token.kind readToken) SymbolTypeConstants.symbolTypeCommentLine))
                                     (not (= (Token.kind readToken) SymbolTypeConstants.symbolTypeCommentStart)))
                                (begin
                                  (set! result GPMessageConstants.gpMsgTokenRead)
                                  (set! done #t)
                                  )
                                (void))
                            )
                          (void)
                          )
                      )
                  )
                (if (> (GOLDParser-pCommentLevel parser) 0)
                    (let ([readToken (last (GOLDParser-pInputTokens parser))])
                      (begin
                        (set-GOLDParser-pInputTokens! parser (drop-right (GOLDParser-pInputTokens parser) 1))
                        (cond
                          [(= (Token.kind readToken) SymbolTypeConstants.symbolTypeCommentStart)
                           (set-GOLDParser-pCommentLevel! (add1 (GOLDParser-pCommentLevel parser)))
                           ]
                          [(= (Token.kind readToken) SymbolTypeConstants.symbolTypeCommentEnd)
                           (set-GOLDParser-pCommentLevel! (- (GOLDParser-pCommentLevel parser) 1))
                           ]
                          [(= (Token.kind readToken) SymbolTypeConstants.symbolTypeEnd)
                           (begin
                             (set! result GPMessageConstants.gpMsgCommentError)
                             (set! done #f)
                             )
                           ]
                          )
                        )
                      )
                    (let ([readToken (last (GOLDParser-pInputTokens parser))])
                      (cond
                        [(= (Token.kind readToken) SymbolTypeConstants.symbolTypeCommentStart)
                         (begin
                           (set-GOLDParser-pCommentLevel! parser (add1 (GOLDParser-pCommentLevel parser)))
                           (set-GOLDParser-pInputTokens! parser (drop-right (GOLDParser-pInputTokens parser) 1))
                           )
                         ]
                        [(= (Token.kind readToken) SymbolTypeConstants.symbolTypeCommentLine)
                         (begin
                           (set-GOLDParser-pInputTokens! parser (drop-right (GOLDParser-pInputTokens parser) 1))
                           (_GOLDParser.discardRestOfLine parser)
                           )
                         ]
                        [(= (Token.kind readToken) SymbolTypeConstants.symbolTypeError)
                         (begin
                           (set! result GPMessageConstants.gpMsgLexicalError)
                           (set! done #t)
                           )
                         ]
                        [else
                         (let ([parseResult (_GOLDParser.parseToken parser readToken)])
                           (cond
                             [(= parseResult ParseResultConstants.parseResultAccept)
                              (begin
                                (set! result GPMessageConstants.gpMsgAccept)
                                (set! done #t)
                                )
                              ]
                             [(= parseResult ParseResultConstants.parseResultInternalError)
                              (begin
                                (set! result GPMessageConstants.gpMsgInternalError)
                                (set! done #t)
                                )
                              ]
                             [(= parseResult ParseResultConstants.parseResultReduceEliminated)
                              (begin
                                (set! result GPMessageConstants.gpMsgReductionTrimmed)
                                (set! done #t)
                                )
                              ]
                             [(= parseResult ParseResultConstants.parseResultReduceNormal)
                              (begin
                                (set! result GPMessageConstants.gpMsgReduction)
                                (set! done #t)
                                )
                              ]
                             [(= parseResult ParseResultConstants.parseResultShift)
                              (begin
                                (set-GOLDParser-pInputTokens! parser (drop-right (GOLDParser-pInputTokens parser) 1))
                                (set! result GPMessageConstants.gpMsgShift)
                                (set! done #t)
                                )
                              ]
                             [(= parseResult ParseResultConstants.parseResultSyntaxError)
                              (begin
                                (set! result GPMessageConstants.gpMsgSyntaxError)
                                (set! done #t)
                                )
                              ]
                             )
                           )
                         ]
                        )
                      )
                    )
                )
            )
          )
      result
      )))

; This private function analyzes a token and either:
;  1. Makes a SINGLE reduction and pushes a complete Reduction object on the stack
;  2. Accepts the token and shifts
;  3. Errors and places the expected symbol indexes in the Tokens list
; The Token is assumed to be valid and WILL be checked
; If an action is performed that requires controlt to be returned to the user, the function returns true.
; The Message parameter is then set to the type of action.
(define (_GOLDParser.parseToken parser nextToken)
  (letrec ([returnInt -1]
           [lrAct (list-ref (GOLDParser-pActionTable parser) (GOLDParser-currentLALR parser))]
           [index (LRActionTable.actionIndexForSymbol lrAct (Symbol-tableIndex (Token-parentSymbol nextToken)))]
           [head '()])
    (begin
      (if (not (= index -1))
          (begin
            (set-GOLDParser-pHaveReductions! parser #f)
            (set-GOLDParser-pTokens! parser '())
            (let ([ac (LRAction-actionConstant (LRActionTable.item lrAct index))])
              (cond
                [(= ac ActionConstants.actionAccept)
                 (begin
                   (set-GOLDParser-pHaveReductions! parser #t)
                   (set! returnInt ParseResultConstants.parseResultAccept)
                   )
                 ]
                [(= ac ActionConstants.actionShift)
                 (begin
                   (set-GOLDParser-currentLALR! parser (LRAction-value (LRActionTable.item lrAct index)))
                   (set-Token-state! nextToken (GOLDParser-currentLALR parser))
                   (set-GOLDParser-stack! parser (append (GOLDParser-stack parser) (list nextToken)))
                   (set! returnInt ParseResultConstants.parseResultShift)
                   )
                 ]
                [(= ac ActionConstants.actionReduce)
                 (begin 
                   (letrec ([ruleIndex (LRAction-value (LRActionTable.item lrAct index))]
                            [currentRule (list-ref (GOLDParser-pRuleTable parser) ruleIndex)])
                     (if (and (GOLDParser-pTrimReductions parser) (Rule.containsOneNonTerminal currentRule))
                         (let ([dummy #f]) ; creepy
                           (begin
                             (set! head (last (GOLDParser-stack parser)))
                             (set-GOLDParser-stack! parser (drop-right (GOLDParser-stack parser) 1))
                             (set-Token-parentSymbol! head (Rule-pRuleNonTerminal currentRule))
                             (set! returnInt ParseResultConstants.parseResultReduceEliminated)
                             )
                           )
                         (begin
                           (set-GOLDParser-pHaveReductions! parser #t)
                           (let ([newReduction (Reduction 
                                                (make-list (Rule.getSymbolCount currentRule) #f)
                                                (Rule.getSymbolCount currentRule)
                                                currentRule
                                                void
                                                )])
                             (set-Reduction-parentRule! newReduction currentRule)
                             (set-Reduction-pTokenCount! newReduction (Rule.getSymbolCount currentRule))
                             (for ([i (reverse (range (- (Reduction-pTokenCount newReduction) 0)))])
                               (let ([curTok (last (GOLDParser-stack parser))])
                                 (begin
                                   (set-GOLDParser-stack! parser (drop-right (GOLDParser-stack parser) 1))
                                   (Reduction.setToken newReduction i curTok)
                                   )
                                 )
                               )
                             (set! head (Token void newReduction (Rule-pRuleNonTerminal currentRule)))
                             (set-Token-data! head newReduction)
                             (set-Token-parentSymbol! head (Rule-pRuleNonTerminal currentRule))
                             (set! returnInt ParseResultConstants.parseResultReduceNormal)
                             )
                           )
                         )
                     (letrec
                         ([topStack (last (GOLDParser-stack parser))]
                          [index (Token-state topStack)]
                          [lrAct (list-ref (GOLDParser-pActionTable parser) index)]
                          [n (LRActionTable.actionIndexForSymbol lrAct (Symbol-tableIndex (Rule-pRuleNonTerminal currentRule)))]
                          )
                       (if (not (= n -1))
                           (begin
                             (set-GOLDParser-currentLALR! parser (LRAction-value (LRActionTable.item lrAct n)))
                             (set-Token-state! head (GOLDParser-currentLALR parser))
                             (set-GOLDParser-stack! parser (append (GOLDParser-stack parser) (list head)))
                             )
                           (begin
                             (set! returnInt ParseResultConstants.parseResultInternalError)
                             )
                           )
                       )
                     )
                   )
                 ]
                )
              )
            )
          (begin
            (set-GOLDParser-pTokens! parser '())
            (let ([lrAct (list-ref (GOLDParser-pActionTable parser) (GOLDParser-currentLALR parser))])
              (for ([i (range (- (LRActionTable-memberCount lrAct) 0))])
                (if (= (Symbol-kind (LRAction-pSymbol (LRActionTable.item lrAct i))) SymbolTypeConstants.symbolTypeTerminal)
                    (begin
                      (set! head (Token void "" (LRAction-pSymbol (LRActionTable.item lrAct i))))
                      (set-GOLDParser-pTokens! parser (append (GOLDParser-pTokens parser) (list head)))
                      )
                    (void)
               
                    )
                ))
            (set! returnInt ParseResultConstants.parseResultSyntaxError)
            )
          )
      returnInt
      )
    ))

; This function implements the DFA algorithm and returns a token to the LALR state
; machine
(define (_GOLDParser.retrieveToken parser source)
  (letrec ([ch 0]
           [n 0]
           [currentDFA 0]
           [target 0]
           [found #f]
           [done #f]
           [peekCount 0]
           [charSetIndex 0]
           [currentPosition 0]
           [lastAcceptState 0]
           [lastAcceptPosition 0]
           [inWhiteSpaceCharSet #f]
           [result (Token void void void)]
           [peekResult (peek-char (GOLDParser-pSource parser))])
    (begin
      (set! currentDFA (GOLDParser-initialDFAState parser))
      (set! currentPosition 1)
      (set! lastAcceptState -1)
      (set! lastAcceptPosition -1)
      (if (not (eq? peekResult eof))
          (if (not done)
              (do ([dummy #f]) ((eq? done #t))
                (begin
                  (set! ch (peek-char (GOLDParser-pSource parser) peekCount))
                  (set! peekCount (add1 peekCount))
                  (if (or (eq? ch "") (eq? ch eof))
                      (set! found #f)
                      (begin
                        (set! n 0)
                        (set! found #f)
                        (let ([faTmp (list-ref (GOLDParser-pDFA parser) currentDFA)]
                              [pdfa (GOLDParser-pDFA parser)])
                          (if (and (< n (FAState.edgeCount faTmp)) (not found))
                              (do ([dummy #f])
                                ((or (>= n (FAState.edgeCount faTmp)) found))
                                (begin
                                  (set! charSetIndex (FAEdge-chars (FAState.edge faTmp n)))
                                  (let ([sT (list-ref (GOLDParser-pCharacterSetTable parser) charSetIndex)])
                                    (for ([i (range (- (string-length sT) 0))])
                                      (let ([k (string-ref sT i)]
                                            [x ch])
                                        (if (char=? k (integer->char 10))
                                            (begin
                                              (set! inWhiteSpaceCharSet #t)
                                              (if (char=? x k)
                                                  (if (and (char? (peek-char (GOLDParser-pSource parser) peekCount))
                                                           (not (char-whitespace? (peek-char (GOLDParser-pSource parser) peekCount))))
                                                      (begin
                                                        (set! found #t)
                                                        (set! target (FAEdge-targetIndex (FAState.edge faTmp n)))
                                                        )
                                                      (void))
                                                  (void))
                                              )
                                            (void)
                                            )
                                        )
                                      )
                                    (letrec ([checkerFound #f]
                                             [sTChar ""]
                                             [checker ch])
                                      (begin
                                        (for/and ([i (range (- (string-length sT) 0))])
                                          (begin
                                            (set! sTChar (string-ref sT i))
                                            (if (and (GOLDParser-pIgnoreCase parser) (char-ci=? checker sTChar))
                                                (begin
                                                  (set! checkerFound #t)
                                                  #f
                                                  )
                                                (void))
                                            (if (and (not (GOLDParser-pIgnoreCase parser)) (char=? checker sTChar))
                                                (begin
                                                  (set! checkerFound #t)
                                                  #f
                                                  )
                                                (void))
                                            )
                                          )
                                        (if checkerFound
                                            (begin
                                              (set! found #t)
                                              (set! target (FAEdge-targetIndex (FAState.edge faTmp n)))
                                              )
                                            (void))
                                        )
                                      )
                                    )
                                  
                                  (set! n (add1 n))
                                  )
                                )
                              (void)
                              )
                          )
                        )
                      )
                  (if found
                      (begin

                        (let ([faTmp2 (list-ref (GOLDParser-pDFA parser) target)])
                          (if (not (= (FAState-acceptSymbol faTmp2) -1))
                              (begin
                                (set! lastAcceptState target)
                                (set! lastAcceptPosition currentPosition)
                                )
                              (void)
                              )
                          )
                        (set! currentDFA target)
                        (set! currentPosition (add1 currentPosition))
                        )
                      (begin
                        (set! done #t)
                        (if (= lastAcceptState -1)
                            (if (= (GOLDParser-pCommentLevel parser) 0)
                                (begin
                                  (set-Token-parentSymbol! result (GOLDParser-kErrorSymbol parser))
                                  (set-Token-data! result (read-string 1 (GOLDParser-pSource parser)))
                                  (set! peekCount (- peekCount 2))
                                  )
                                (set! done #f)
                                )
                            (let ([faTmp3 (list-ref (GOLDParser-pDFA parser) lastAcceptState)])
                              (begin
                                (set-Token-parentSymbol! result (SymbolList.getMember (GOLDParser-pSymbolTable parser) (FAState-acceptSymbol faTmp3)))
                                (set-Token-data! result (read-string (max lastAcceptPosition 0) (GOLDParser-pSource parser)))
                                (set! peekCount (- peekCount (+ (max lastAcceptPosition 0) 1)))
                                )
                              )

                            )
                        )
                      )
                  )

                )
              (void)
              )
          (begin
            (set-Token-data! result "")
            (set-Token-parentSymbol! result (GOLDParser-kEndSymbol parser))
            )
          )
      (let ([strTmp (if (eq? void (Token-data result)) "" (Token-data result))]
            [lastNL 0])
        (begin
          (for ([n (range (- (string-length strTmp) 0))])
            (if (char=? (string-ref strTmp n) #\newline)
                (begin
                  (set-GOLDParser-pLineNumber! parser (add1 (GOLDParser-pLineNumber parser)))
                  (set-GOLDParser-pCharacterPos! parser 0)
                  (set! lastNL n)
                  )
                (void)
                )
            )
          (set-GOLDParser-pCharacterPos! parser (+ (GOLDParser-pCharacterPos parser) (string-length (substring strTmp lastNL))))
          )
        )
      )
    result
    ))


; constructing the parser
(define p (GOLDParser (SymbolList '() 0) '() '() '() #hash() '() '() '() '() '() '() '() '() '() '()
                      #t #f '() '() '() '() '() '()))

;(define code (list->string '(#\1 #\+ #\1 #\newline)))
; loading the input file
(require racket/file)
(define code (file->string "d:\\share\\gold\\diverses\\test.sql" #:mode 'text))

; loading the grammar
(define loaded (GOLDParser.loadCompiledGrammar p "d:\\share\\gold\\diverses\\sql.cgt"))

; initializing the parser
(set-GOLDParser-startSymbol! p (hash-ref (GOLDParser-pVariables p) "Start Symbol"))
(define r  (GOLDParser.reset p))
(define opened (GOLDParser.openText p code))

; parsing the input
(define parse
  (lambda ()

    (let ([fertig #f]
          [tree '()])
      (do ([dummy #f])
        ((eq? fertig #t))
        (let ([r (GOLDParser.parse p)]
          
              )
          (cond
            [(= r GPMessageConstants.gpMsgAccept)
             (print "Parser hat eine Aktion beendet.")
             (newline)
             (print "Accept.")(newline)
             (print "LALR State: ")
             (print (GOLDParser-currentLALR p))
             (newline)
             (set! fertig #t)
             (set! tree (GOLDParser-stack p))
             ]
            [(= r GPMessageConstants.gpMsgCommentError)
             (print "Fehler im Kommentar")
             (newline)
             (set! fertig #t)
             ]
            [(= r GPMessageConstants.gpMsgInternalError)
             (print "Interner Fehler")
             (newline)
             (set! fertig #t)
             ]
            [(= r GPMessageConstants.gpMsgLexicalError)
             (print "lexikalischer Fehler")
             (newline)
             (set! fertig #t)
             ]
            [(= r GPMessageConstants.gpMsgNotLoadedError)
             (print "nicht geladen")
             (newline)
             (set! fertig #t)
             ]
            [(= r GPMessageConstants.gpMsgReduction)
             (print "Parser hat eine Aktion beendet.")
             (newline)
             ;(print "Reduktion: ")
             ;(print (GOLDParser.currentReduction p))
             ;(newline)
             (print "LALR State: ")
             (print (GOLDParser-currentLALR p))
             (newline)
             ]
            [(= r GPMessageConstants.gpMsgReductionTrimmed)
             (print "Trim")
             (newline)
             ]
            [(= r GPMessageConstants.gpMsgSyntaxError)
             (print "Syntaxfehler")
             (newline)
             (set! fertig #t)
             ]
            [(= r GPMessageConstants.gpMsgTokenRead)
             (print "Parser hat eine Aktion beendet.")
             (newline)
             (print "Token gelesen: ")
             (let ([currentToken (last (GOLDParser-pInputTokens p))])
               (print currentToken))
             (newline)
             (print "LALR State: ")
             (print (GOLDParser-currentLALR p))
             (newline)
             ]
            [(= r GPMessageConstants.gpMsgShift)
             (print "Parser hat eine Aktion beendet.")
             (newline)
             (print "Shift.")
             (newline)
             (print "LALR State: ")
             (print (GOLDParser-currentLALR p))
             (newline)
             ]

            )
          )
        )
      (last tree)
      ;(print (- #\a 1) )
  )))

; retrieve AST of input
(define ast (parse))

(require racket/function)
; printing the ree
(define (Walk-AST tree tabs)
  (cond
    [(Token? tree)
     (let ([data (Token-data tree)])
       (write (list->string tabs))
       (print "Token ")
       (cond
         [(= (Token.kind tree) SymbolTypeConstants.symbolTypeNonterminal) (print "Nonterminal ")(newline)]
         [(= (Token.kind tree) SymbolTypeConstants.symbolTypeTerminal)
          
          (print "Terminal ")
          (print data)
          (newline)
          ]

         )
       (Walk-AST data (append tabs '(#\tab)))
       (void)
       )]
    
    [(Reduction? tree)
     (let ([data (Reduction-pTokens tree)])
       (write (list->string tabs))
       (print "Reduction ")
       (print (Rule.name (Reduction-parentRule tree)))
       (newline)
       (map (lambda (x) (Walk-AST x (append tabs '(#\tab)))) data)
       (void)
       )]
    [else (void)]
   ))

(Walk-AST ast '())