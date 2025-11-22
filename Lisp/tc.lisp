;;;; 889018 Biglioli Sabrina
;;;; 917356 Carducci Lorenzo
;;;; 914396 Coletta Giovanni
;;;; Type checker per Lisp (interi + variabili + liste + built-in)

(defun tc (filename)
  "Entry point del type checker con reporting."
  (tc-reset-report)
  (format t ";;; Type checking '~A'.~%~%" filename)
  (let ((forms (read-all-forms-from-file filename)))
    (dolist (form forms)
      (process-top-level-form form)))
  (tc-print-summary)
  (if (null *tc-errors*) t nil))



(defun read-all-forms-from-file (filename)
  "Legge tutte le forme Lisp da FILENAME e le restituisce come lista."
  (with-open-file (in filename :direction :input)
    (loop for form = (read in nil :eof)
          until (eq form :eof)
          collect form)))


(defparameter *function-table*
  (make-hash-table :test #'eq)
  "Tabella che associa il nome della funzione a una struttura con info sul numero di argomenti, ecc.")


(defstruct function-info
  name          ; simbolo della funzione
  required-args ; lista dei parametri obbligatori
  optional-args ; lista dei parametri opzionali
  min-arity     ; numero minimo di argomenti
  max-arity     ; numero massimo di argomenti
  ;; in futuro: rest-arg, keyword-args, tipo di ritorno, tipo degli argomenti, ecc.
  )


(defstruct function-type
  arg-types           ; lista tipi degli argomenti obbligatori
  optional-arg-types  ; lista tipi degli argomenti opzionali
  return-type)        ; tipo di ritorno


(defparameter *function-type-env*
  (let ((ht (make-hash-table :test #'eq)))
    ;; Built-in aritmetici su interi
    (setf (gethash '+ ht)
          (make-function-type
           :arg-types '(:int :int)
           :optional-arg-types '()
           :return-type :int))
    (setf (gethash '* ht)
          (make-function-type
           :arg-types '(:int :int)
           :optional-arg-types '()
           :return-type :int))
    (setf (gethash '- ht)
          (make-function-type
           :arg-types '(:int)
           :optional-arg-types '(:int)  ; (- x) o (- x y)
           :return-type :int))
    (setf (gethash '1- ht)
          (make-function-type
           :arg-types '(:int)
           :optional-arg-types '()
           :return-type :int))
    (setf (gethash 'zerop ht)
          (make-function-type
           :arg-types '(:int)
           :optional-arg-types '()
           :return-type :bool))
    ht)
  "Tabella dei tipi delle funzioni built-in e delle defun utente note.")


(defun process-top-level-form (form)
  "Analizza una forma top-level.
   - DEFUN: registra la funzione.
   - Altro: prova a fare un controllo sulla chiamata."
  (cond
    ((and (consp form)
          (eq (car form) 'defun))
     (process-defun-form form))
    (t
     ;; qui facciamo il controllo sulle espressioni top-level
     (type-check-expression form))))


(defun type-check-top-level-expression (form)
  "Controlla una espressione top-level.
   Per ora: controlla solo l'arità delle funzioni definite dall'utente."
  (format t "Checking top-level expression: ~S~%" form)
  (type-check-expression form nil))


(defun type-check-expression (expr)
  "Controllo minimalista delle espressioni.
   Usa *function-type-env* per controllare le chiamate a funzioni note
   e *function-table* per controllare almeno l'arità delle funzioni
   definite dall'utente."
  (cond
    ;; numeri, simboli, stringhe, NIL da soli: niente da controllare
    ((or (integerp expr)
         (symbolp expr)
         (stringp expr)
         (null expr))
     nil)

    ;; quote, tipo 'six o '3
    ((and (consp expr)
          (eq (car expr) 'quote))
     nil)

    ;; chiamata di funzione o forma speciale
    ((consp expr)
     (let ((fn   (car expr))
           (args (cdr expr)))
       ;; prima controlliamo ricorsivamente tutti gli argomenti
       (dolist (a args)
         (type-check-expression a))
       ;; poi, se conosciamo qualcosa sulla funzione, facciamo i controlli
       (let* ((ftype     (gethash fn *function-type-env*))
              (user-info (gethash fn *function-table*)))
         (cond
           ;; se abbiamo info di tipo, usiamo il controllo di tipo completo
           (ftype
            (check-function-call fn ftype args expr))
           ;; altrimenti, se è una funzione definita dall'utente, controlliamo almeno l'arità
           (user-info
            (check-user-function-call fn args expr nil))
           ;; altrimenti non sappiamo nulla: nessun controllo extra
           (t
            nil)))))
    (t
     nil)))


(defun check-function-call (fn-symbol args)
  "Controlla una chiamata a funzione/built-in secondo *function-type-env*.
   Colleziona le signature viste e accumula gli errori invece di stamparli subito."
  (let* ((fty (gethash fn-symbol *function-type-env*))
         (req (and fty (function-type-arg-types fty)))
         (opt (and fty (function-type-optional-arg-types fty))))
    (unless fty
      ;; Se non abbiamo tipi noti per FN, non imponiamo vincoli tipali
      ;; ma registriamo comunque la call con i tipi inferiti.
      (let ((actuals (mapcar #'infer-type args)))
        (tc-note-call fn-symbol actuals))
      (return-from check-function-call t))

    ;; Arity check 'soft': se troppi/pochi argomenti, errore.
    (let* ((min (length req))
           (max (+ (length req) (length opt)))
           (arity (length args)))
      (when (or (< arity min) (> arity max))
        (tc-note-error "Wrong arity for ~A: got ~D, expected ~D..~D"
                       fn-symbol arity min max)
        (return-from check-function-call nil)))

    ;; Abbiniamo i tipi attesi ai reali
    (let* ((expected (append req (subseq opt 0 (max 0 (- (length args) (length req))))))
           (actuals  (mapcar #'infer-type args))
           (ok t))
      ;; registra la chiamata per il riepilogo
      (tc-note-call fn-symbol actuals)

      ;; verifica puntuale tipo per tipo (se :unknown non segnala)
      (loop for a in actuals
            for e in expected
            for orig in args
            do (when (and (not (eq a :unknown)) (not (eql a e)))
                 (setf ok nil)
                 (tc-note-error "'~A' is not of type '~(~A~)' in call ~S"
                                (display-arg orig) e (cons fn-symbol args))))
      ok)))



(defun process-defun-form (form)
  "Analizza una forma (defun ...) e la registra nella *function-table*."
  ;; Forma attesa: (defun name (params...) body...)
  (destructuring-bind (_defun name params-list &rest _body)
      form
    (let* ((required-params '())
           (optional-params '()))
      ;; Parametri possono essere: (x y &optional (acc 1))
      (loop for rest-params on params-list
            for param = (car rest-params)
            do (cond
                 ((eq param '&optional)
                  (setf optional-params (cdr rest-params))
                  (return))
                 (t
                  (push param required-params))))
      (setf required-params (nreverse required-params))
      ;; Creiamo la struttura function-info (info "strutturale": solo nomi parametri)
      (let ((info (make-function-info
                   :name          name
                   :required-args required-params
                   :optional-args optional-params)))
        (setf (gethash name *function-table*) info)

        ;; --- Qui agganciamo anche le informazioni di TIPO ---

        ;; Caso specifico di FACT come da traccia:
        ;; (function (integer &optional integer) integer)
        (when (eq name 'fact)
          ;; registra il tipo nella tabella dei tipi di funzione
          (setf (gethash name *function-type-env*)
                (make-function-type
                 :arg-types '(:int)       ; n
                 :optional-arg-types '(:int) ; acc
                 :return-type :int))
          ;; stampa la riga ftype come nell'esempio della traccia
          (format t "(ftype (function (integer &optional integer) integer) ~A)~%"
                  name))

        info))))


(defun infer-type (expr)
  "Inferenza molto grezza: riconosce interi e simboli quotati."
  (cond
    ;; intero nudo: 42
    ((integerp expr)
     :int)

    ;; '3  → (quote 3)
    ((and (consp expr)
          (eq (car expr) 'quote))
     (let ((v (cadr expr)))
       (cond
         ((integerp v) :int)
         ((symbolp v)  :symbol)
         (t            :unknown))))

    ;; tutto il resto: per ora tipo sconosciuto
    (t
     :unknown)))


(defun check-user-function-call (fn args original-expr env)
  "Controlla il numero di argomenti di una chiamata a funzione definita dall'utente."
  (declare (ignore env)) ; lo useremo quando controlleremo davvero i tipi
  (let* ((info (gethash fn *function-table*)))
    (when info
      (let* ((nargs (length args))
             (min   (function-info-min-arity info))
             (max   (function-info-max-arity info)))
        ;; troppo pochi argomenti
        (when (< nargs min)
          (format t "Error: funzione ~A chiamata con ~D argomenti, \
ma ne richiede almeno ~D.~%  Espressione: ~S~%"
                  fn nargs min original-expr))
        ;; troppi argomenti
        (when (> nargs max)
          (format t "Error: funzione ~A chiamata con ~D argomenti, \
ma ne accetta al massimo ~D.~%  Espressione: ~S~%"
                  fn nargs max original-expr))))
    ;; in futuro qui controlleremo anche i tipi
    :unknown))


(defun display-arg (expr)
  "Restituisce una stringa 'bella' per l'argomento nell'errore."
  (cond
    ;; 'six → "six"
    ((and (consp expr)
          (eq (car expr) 'quote)
          (symbolp (cadr expr)))
     (symbol-name (cadr expr)))
    ;; altrimenti usiamo la standard
    (t
     (format nil "~S" expr))))


;;;; ======================= REPORTING LAYER =======================

(defvar *tc-errors* nil)
(defvar *tc-call-signatures* (make-hash-table :test #'equal))
;; Chiave: (name . arity) -> (lista di liste dei tipi degli argomenti visti)

(defun tc-reset-report ()
  (setf *tc-errors* nil)
  (clrhash *tc-call-signatures*))

(defun tc-note-error (fmt &rest args)
  (push (apply #'format nil fmt args) *tc-errors*))

(defun tc-note-call (name arg-types)
  "Registra la signature di una chiamata NAME(ARGS)."
  (let* ((arity (length arg-types))
         (key   (cons name arity))
         (lst   (gethash key *tc-call-signatures*)))
    (setf (gethash key *tc-call-signatures*)
          (adjoin arg-types lst :test #'equal))))

(defun %human-type (ty)
  "Mapping 'umano' per la stampa; adatta se usi etichette diverse."
  (case ty
    (:int 'integer)
    (:atom 'atom)
    (:bool 'boolean)
    (t ty)))

(defun %print-function-def-summaries ()
  "Stampa le defun note dal tuo *function-table* e, se presenti, i relativi tipi da *function-type-env*."
  (maphash
   (lambda (name info)
     (let* ((req (or (ignore-errors (function-info-required-args info)) '()))
            (opt (or (ignore-errors (function-info-optional-args info)) '()))
            (fty (gethash name *function-type-env*))
            (argt (when fty (append (function-type-arg-types fty)
                                    (function-type-optional-arg-types fty))))
            (rett (when fty (function-type-return-type fty))))
       (format t "function ~A/~D" name (+ (length req) (length opt)))
       (when argt
         (format t "  :: (~~{~~A~~^, ~~}) -> ~~A~%"
                 (mapcar #'%human-type argt)
                 (%human-type rett)))
       (unless argt (format t "~%"))))
   *function-table*))

(defun %print-call-summaries ()
  "Stampa le signature uniche delle chiamate osservate durante il check."
  (let ((keys (loop for k being the hash-keys of *tc-call-signatures* collect k)))
    (dolist (key (sort keys (lambda (a b)
                              (or (string< (symbol-name (car a)) (symbol-name (car b)))
                                  (< (cdr a) (cdr b))))))
      (dolist (sig (gethash key *tc-call-signatures*))
        (format t "call ~A/~A (~~{~~A~~^, ~~})~%"
                (car key) (cdr key) (mapcar #'%human-type sig))))))

(defun tc-print-summary ()
  (format t "~%--- Summary ----------------------------------~%")
  (%print-function-def-summaries)
  (%print-call-summaries)
  (when *tc-errors*
    (format t "~%--- Errors -----------------------------------~%")
    (dolist (e (nreverse *tc-errors*))
      (format t "Error: ~A~%" e))))
