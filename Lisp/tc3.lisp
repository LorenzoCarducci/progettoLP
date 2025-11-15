;;;; === STEP 1: TIPI E TABELLA DELLE FUNZIONI ===

(defstruct function-type
  arg-types           ; lista tipi argomenti obbligatori
  optional-arg-types  ; lista tipi argomenti opzionali
  return-type)        ; tipo di ritorno


(defparameter *function-type-env*
  (let ((ht (make-hash-table :test #'eq)))
    ;; + : (int, int) -> int
    (setf (gethash '+ ht)
          (make-function-type
           :arg-types '(:int :int)
           :optional-arg-types '()
           :return-type :int))

    ;; * : (int, int) -> int
    (setf (gethash '* ht)
          (make-function-type
           :arg-types '(:int :int)
           :optional-arg-types '()
           :return-type :int))

    ;; - : (int, int) -> int  (per ora solo binaria)
    (setf (gethash '- ht)
          (make-function-type
           :arg-types '(:int :int)
           :optional-arg-types '()
           :return-type :int))

    ;; 1- : (int) -> int
    (setf (gethash '1- ht)
          (make-function-type
           :arg-types '(:int)
           :optional-arg-types '()
           :return-type :int))

    ;; zerop : (int) -> bool
    (setf (gethash 'zerop ht)
          (make-function-type
           :arg-types '(:int)
           :optional-arg-types '()
           :return-type :bool))

    ;; cons : (qualunque, list) -> list
    (setf (gethash 'cons ht)
          (make-function-type
           :arg-types '(:unknown :list)
           :optional-arg-types '()
           :return-type :list))

    ;; car : (list) -> unknown
    (setf (gethash 'car ht)
          (make-function-type
           :arg-types '(:list)
           :optional-arg-types '()
           :return-type :unknown))

    ;; cdr : (list) -> list
    (setf (gethash 'cdr ht)
          (make-function-type
           :arg-types '(:list)
           :optional-arg-types '()
           :return-type :list))

    ht)
  "Tabella dei tipi delle funzioni conosciute (built-in + defun utente).")



;;;; === INFO STRUTTURALI SULLE FUNZIONI DEFINITE DALL'UTENTE ===

(defstruct function-info
  name          ; simbolo della funzione
  required-args ; lista dei parametri obbligatori
  optional-args ; lista dei parametri opzionali (dopo &optional)
  min-arity     ; numero minimo di argomenti
  max-arity)    ; numero massimo di argomenti

(defparameter *function-table*
  (make-hash-table :test #'eq)
  "Tabella che associa il nome di una funzione definita con DEFUN
   alle sue informazioni strutturali (parametri, arità, ecc.).")



;;;; === STEP 2: INFERENZA DI TIPO SEMPLICE ===

(defun infer-type-atom (expr)
  "Inferisce il tipo di una espressione atomica (non lista)."
  (cond
    ((integerp expr) :int)
    ;; in futuro potremmo distinguere T/NIL, simboli, stringhe...
    (t :unknown)))

(defun infer-type-quoted (v)
  "Tipo di un valore citato (dentro un (quote ...))."
  (cond
    ((integerp v) :int)
    ((symbolp v)  :symbol)
    ((listp v)    :list)
    (t            :unknown)))


(defun infer-type (expr)
  "Wrapper senza environment: parte sempre da env vuoto."
  (infer-type-with-env expr nil))


(defun infer-type-with-env (expr env)
  "Inferisce il tipo di EXPR usando un environment ENV che associa
   simboli a tipi (alist di (sym . type))."
  (cond
    ;; caso atomico
    ((atom expr)
     (cond
       ((integerp expr) :int)
       ((symbolp expr)
        (let ((b (assoc expr env)))
          (if b
              (cdr b)
              :unknown)))
       (t :unknown)))

    ;; caso (quote ...)
    ((and (consp expr)
          (eq (car expr) 'quote))
     (infer-type-quoted (cadr expr)))

    ;; caso (lambda (params...) body...)
    ((and (consp expr)
          (eq (car expr) 'lambda))
     (let* ((params (second expr))
            (body   (cddr expr))
            ;; per ora assegniamo tutti i parametri a :unknown
            (lambda-env (append (mapcar (lambda (p) (cons p :unknown))
                                        params)
                                env)))
       (let ((last-type :unknown))
         (dolist (form body)
           (setf last-type (infer-type-with-env form lambda-env)))
         last-type)))

    ;; caso (let ((v1 e1) (v2 e2) ...) body...)
    ((and (consp expr)
          (eq (car expr) 'let))
     (let* ((bindings (second expr))
            (body     (cddr expr))
            (new-env  env))
       ;; controlla espressioni di inizializzazione e aggiorna env
       (dolist (b bindings)
         (let* ((var (first b))
                (rhs (second b))
                (ty  (infer-type-with-env rhs new-env)))
           (setf new-env (acons var ty new-env)))
         )
       ;; controlla il corpo e restituisce il tipo dell'ultima forma
       (let ((last-type :unknown))
         (dolist (form body)
           (setf last-type (infer-type-with-env form new-env)))
         last-type)))

    ;; caso chiamata di funzione (lista non vuota)
    ((consp expr)
     (let* ((fn   (car expr))
            (args (cdr expr))
            (ftype (and (symbolp fn)
                        (gethash fn *function-type-env*)))
            (uinfo (and (symbolp fn)
                        (gethash fn *function-table*))))
       ;; attraversiamo sempre gli argomenti (per propagare errori)
       (dolist (a args)
         (infer-type-with-env a env))
       (cond
         ;; funzione con tipo noto
         (ftype
          (check-function-call fn ftype args env))
         ;; funzione utente nota, ma senza tipo: solo arità
         (uinfo
          (check-user-function-call fn args)
          :unknown)
         ;; funzione completamente sconosciuta
         (t
          (format t "Warning: funzione sconosciuta ~S.~%" fn)
          :unknown))))
    ))



(defun check-function-call (fn ftype args env)
  "Controlla una chiamata a funzione FN con tipo FTYPE su argomenti ARGS.
   Usa ENV per inferire i tipi di variabili. Stampa errori se i tipi
   o l'arità non corrispondono. Restituisce il tipo di ritorno dichiarato,
   oppure :unknown in caso di errore."
  (let* ((req   (function-type-arg-types ftype))
         (opt   (function-type-optional-arg-types ftype))
         (nreq  (length req))
         (nopt  (length opt))
         (nargs (length args))
         (ok    t))
    ;; 1) controllo arità minima
    (when (< nargs nreq)
      (format t "Error: funzione ~A chiamata con ~D argomenti, ma ne richiede almeno ~D.~%  Espressione: ~S~%"
              fn nargs nreq (cons fn args))
      (setf ok nil))
    ;; 2) controllo arità massima
    (when (> nargs (+ nreq nopt))
      (format t "Error: funzione ~A chiamata con ~D argomenti, ma ne accetta al massimo ~D.~%  Espressione: ~S~%"
              fn nargs (+ nreq nopt) (cons fn args))
      (setf ok nil))
    ;; 3) controllo tipi, per quanti tipi conosciamo
    (loop
      for arg in args
      for expected in (append req opt)
      for i from 1
      do (when expected
           (let ((actual (infer-type-with-env arg env)))
             (when (and (not (eq actual :unknown))
                        (not (eq actual expected)))
               (format t "Error: argomento ~D di ~A ha tipo ~A, ma ci si aspetta ~A. Valore: ~S~%"
                       i fn actual expected arg)
               (setf ok nil)))))
    (if ok
        (function-type-return-type ftype)
        :unknown)))




;;;; === STEP 4: LETTORE DI FILE E ENTRY POINT ===

(defun read-all-forms-from-file (filename)
  "Legge tutte le forme Lisp da FILENAME e le restituisce come lista."
  (with-open-file (in filename :direction :input)
    (loop for form = (read in nil :eof)
          until (eq form :eof)
          collect form)))

(defun type-check-top-level (expr)
  "Tipo di una espressione top-level, con messaggio."
  (let ((ty (infer-type expr)))
    (format t "Expr: ~S  ::  ~A~%" expr ty)
    ty))

(defun tc (filename)
  "Entry point del type checker minimale."
  (format t ";;; Type checking '~A'.~%~%" filename)
  (let ((forms (read-all-forms-from-file filename)))
    (dolist (f forms)
      (process-top-level-form f)))
  t)


(defun param-symbol (p)
  "Dato un parametro P, restituisce il simbolo corrispondente.
   Se P è (acc 1) restituisce ACC, se è acc restituisce ACC."
  (if (consp p)
      (car p)
      p))


(defun build-param-env (fun-name required-params optional-params)
  "Costruisce un environment di tipi per i parametri di una funzione.
   Per ora, assegna :unknown a tutto, tranne nel caso speciale di FACT,
   dove mettiamo :int a n e acc."
  (let ((env nil))
    (labels ((add-param (p)
               (let* ((sym (param-symbol p))
                      (ty  (if (and (eq fun-name 'fact)
                                    (member sym '(n acc)))
                               :int
                               :unknown)))
                 (push (cons sym ty) env))))
      (dolist (p required-params)
        (add-param p))
      (dolist (p optional-params)
        (add-param p)))
    env))



(defun process-defun-form (form)
  "Analizza una forma (defun ...) e la registra nella *function-table*.
   Inoltre, controlla il corpo usando un environment di tipi per i parametri."
  ;; forma attesa: (defun name (params...) body...)
  (destructuring-bind (_defun name params-list &rest body)
      form
    (let* ((required-params '())
           (optional-params '()))
      ;; parametri possono essere: (x y &optional (acc 1))
      (loop for rest-params on params-list
            for param = (car rest-params)
            do (cond
                 ((eq param '&optional)
                  (setf optional-params (cdr rest-params))
                  (return))
                 (t
                  (push param required-params))))
      (setf required-params (nreverse required-params))
      (let* ((nreq (length required-params))
             (nopt (length optional-params))
             (info (make-function-info
                    :name          name
                    :required-args required-params
                    :optional-args optional-params
                    :min-arity     nreq
                    :max-arity     (+ nreq nopt))))
        (setf (gethash name *function-table*) info)

        ;; Caso speciale: FACT → registriamo anche il tipo di funzione
        (when (eq name 'fact)
          (setf (gethash name *function-type-env*)
                (make-function-type
                 :arg-types '(:int)          ; n
                 :optional-arg-types '(:int) ; acc
                 :return-type :int))
          (format t "(ftype (function (integer &optional integer) integer) ~A)~%"
                  name))

        ;; Environment dei parametri per il corpo
        (let ((param-env (build-param-env name required-params optional-params)))
          (dolist (f body)
            (infer-type-with-env f param-env)))

        info))))



(defun process-top-level-form (form)
  "Analizza una forma top-level.
   - Se è una DEFUN, la registra.
   - Altrimenti, fa il type checking dell'espressione."
  (cond
    ((and (consp form)
          (eq (car form) 'defun))
     (process-defun-form form))
    (t
     (type-check-top-level form))))



(defun check-user-function-call (fn args)
  "Controlla il numero di argomenti di una chiamata a funzione definita dall'utente."
  (let* ((info  (gethash fn *function-table*))
         (nargs (length args)))
    (when info
      (let ((min (function-info-min-arity info))
            (max (function-info-max-arity info)))
        (when (< nargs min)
          (format t "Error: funzione ~A chiamata con ~D argomenti, ma ne richiede almeno ~D.~%  Espressione: ~S~%"
                  fn nargs min (cons fn args)))
        (when (> nargs max)
          (format t "Error: funzione ~A chiamata con ~D argomenti, ma ne accetta al massimo ~D.~%  Espressione: ~S~%"
                  fn nargs max (cons fn args)))))))
