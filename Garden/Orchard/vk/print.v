(** * Verified Debug printer for the pinned verifying-key description.

    A structural printer from the model's compiled system
    ([OrchardCompiledCheck.compiled], the [Plonkish.Compile.compile] output
    the twelve parity certificates pin) plus the pinned literals of
    [vk/data.v], to the byte string of Rust's [Debug] rendering of
    [vk.pinned()].  The printer is parameterized on the alternate-form flag
    [alt], mirroring [core::fmt]: [alt = true] yields the pretty [{:#?}]
    rendering (the in-tree dump [circuit_description_fixed], the T1 parity
    target), [alt = false] the compact [{:?}] rendering (the string [s]
    hashed into [transcript_repr] by [keygen_vk],
    [halo2_proofs/src/plonk.rs]).

    Mirrored [Debug] implementations, with the [core::fmt] builder layout
    ([{:#?}]: 4-space indent per nesting level, one entry per line, a
    trailing comma on every entry, closer at the parent indent; [{:?}]:
    [Name { f: v, g: w }] / [Name(v, w)] / [[v, w]] with [", "]
    separators):

    - field elements ([pasta_curves] [Fp]/[Fq]): [0x] + exactly 64
      lowercase hex digits, big-endian of the canonical residue; inline in
      both forms (the impl writes directly, ignoring the alternate flag);
    - affine points: [(x, y)] with field-element coordinates, inline in
      both forms;
    - [Expression] ([halo2 plonk/circuit.rs]): [Sum]/[Product]/[Negated]/
      [Scaled]/[Constant] as tuple structs; query leaves as structs with
      fields [query_index], [column_index], [rotation] — [query_index] is
      resolved by position in the pinned keygen-order query table of the
      leaf's column kind (the model does not carry query indices);
    - [Rotation]: derived tuple struct over a signed decimal;
    - [Column { index, column_type }] with the bare kind marker
      ([Advice]/[Fixed]/[Instance]);
    - [PinnedGates]: one flat list of all gate polynomials;
    - [PinnedConstraintSystem]: derived, so fields render in declaration
      order ([num_*], [gates], [advice_queries], [instance_queries],
      [fixed_queries], [permutation], [lookups], [constants],
      [minimum_degree]);
    - [PinnedEvaluationDomain { k, extended_k, omega }],
      [permutation::Argument { columns }], [lookup::Argument
      { input_expressions, table_expressions }],
      [permutation::VerifyingKey { commitments }], and the quoted [&str]
      moduli.

    The gate list is [printed_gates]: the compiled gates with the deployed
    builder's top-level product association restored on the two gates whose
    modeled association differs (the flattened-fingerprint parity
    certificate [gate_polynomials_match] compares modulo exactly this
    re-association); [printed_gates_gate_fp] proves the fingerprints are
    unchanged, and the T1 byte parity ([vk/parity.v]) certifies the
    printed bytes against the deployed dump. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Garden.Field.Field.
Require Import Garden.Halo2.main.
Require Import Garden.Halo2.serialize.
Require Import Garden.Halo2.plonkish.main.
Require Import Garden.Halo2.plonkish.poly_domain.
Require Import Garden.Orchard.compiled.pinned.
Require Import Garden.Orchard.compiled.check.
Require Import Garden.Orchard.vk.data.

Import ListNotations.
Import Plonkish.
Local Open Scope Z_scope.

Module VkPinnedPrint.

(** ** String-building primitives *)

Definition nl : PrimString.string := PrimString.make 1 10%uint63.
Definition dquote : PrimString.string := PrimString.make 1 34%uint63.

(** Balanced pairwise concatenation of a fragment list: linear total work
    per round, logarithmically many rounds. *)
Fixpoint join_pairs (l : list PrimString.string) : list PrimString.string :=
  match l with
  | a :: b :: rest => PrimString.cat a b :: join_pairs rest
  | _ => l
  end.

Fixpoint join_go (fuel : nat) (l : list PrimString.string)
    : PrimString.string :=
  match l with
  | [] => ""%pstring
  | [s] => s
  | _ =>
      match fuel with
      | O => ""%pstring
      | S fuel => join_go fuel (join_pairs l)
      end
  end.

Definition join (l : list PrimString.string) : PrimString.string :=
  join_go 64 l.

(** Indentation strings, 4 spaces per level ([core::fmt]'s pretty unit),
    memoized up to depth 32 (the dump's maximum is 19). *)
Fixpoint indents_go (n : nat) (cur : PrimString.string)
    : list PrimString.string :=
  match n with
  | O => [cur]
  | S m => cur :: indents_go m (PrimString.cat cur "    ")
  end.

Definition indents : list PrimString.string := indents_go 32 ""%pstring.

Definition ind (d : nat) : PrimString.string := List.nth d indents ""%pstring.

Definition digit (d : Z) : PrimString.string :=
  if d =? 0 then "0" else if d =? 1 then "1" else if d =? 2 then "2"
  else if d =? 3 then "3" else if d =? 4 then "4" else if d =? 5 then "5"
  else if d =? 6 then "6" else if d =? 7 then "7" else if d =? 8 then "8"
  else "9".

Fixpoint dec_go (fuel : nat) (n : Z) (acc : PrimString.string)
    : PrimString.string :=
  match fuel with
  | O => acc
  | S fuel =>
      let acc := PrimString.cat (digit (n mod 10)) acc in
      if n / 10 =? 0 then acc else dec_go fuel (n / 10) acc
  end.

(** Signed decimal (the [usize]/[u32]/[i32] Debug rendering). *)
Definition dec_Z (n : Z) : PrimString.string :=
  if n <? 0 then PrimString.cat "-" (dec_go 40 (- n) ""%pstring)
  else dec_go 40 n ""%pstring.

Definition hexdigit (d : Z) : PrimString.string :=
  if d =? 0 then "0" else if d =? 1 then "1" else if d =? 2 then "2"
  else if d =? 3 then "3" else if d =? 4 then "4" else if d =? 5 then "5"
  else if d =? 6 then "6" else if d =? 7 then "7" else if d =? 8 then "8"
  else if d =? 9 then "9" else if d =? 10 then "a" else if d =? 11 then "b"
  else if d =? 12 then "c" else if d =? 13 then "d" else if d =? 14 then "e"
  else "f".

Fixpoint hex_go (fuel : nat) (n : Z) (acc : PrimString.string)
    : PrimString.string :=
  match fuel with
  | O => acc
  | S fuel => hex_go fuel (n / 16) (PrimString.cat (hexdigit (n mod 16)) acc)
  end.

(** The field-element Debug rendering: [0x] + exactly 64 lowercase hex
    digits, big-endian of the canonical residue (the 32 canonical
    little-endian repr bytes printed in reverse), inline in both forms. *)
Definition hex64 (n : Z) : PrimString.string :=
  PrimString.cat "0x" (hex_go 64 n ""%pstring).

(** ** Reversed-accumulator emission

    Printer functions push fragments onto the front of an accumulator; the
    final string is the balanced join of the reversed accumulator. *)

Definition emit (s : PrimString.string) (acc : list PrimString.string)
    : list PrimString.string :=
  s :: acc.

(** ** Container combinators (the [core::fmt] builders)

    [d] is the container's nesting depth: its opener starts at the current
    cursor, its pretty entries are laid out at indent [S d], its pretty
    closer at indent [d].  Compact containers are inline. *)

(** Opener for tuple structs, tuples and lists: [opener] is ["Name("],
    ["("] or ["["]. *)
Definition copen (alt : bool) (d : nat) (opener : PrimString.string)
    (acc : list PrimString.string) : list PrimString.string :=
  let acc := emit opener acc in
  if alt then emit (ind (S d)) (emit nl acc) else acc.

(** Separator between entries or fields. *)
Definition csep (alt : bool) (d : nat) (acc : list PrimString.string)
    : list PrimString.string :=
  if alt then emit (ind (S d)) (emit nl (emit "," acc)) else emit ", " acc.

(** Closer for tuple structs, tuples and lists: [closer] is [")"] or
    ["]"]; pretty adds the trailing comma on the last entry. *)
Definition cclose (alt : bool) (d : nat) (closer : PrimString.string)
    (acc : list PrimString.string) : list PrimString.string :=
  if alt then emit closer (emit (ind d) (emit nl (emit "," acc)))
  else emit closer acc.

(** Struct opener/closer ([debug_struct]): compact form spaces the braces
    ([Name { f: v }]). *)
Definition sopen (alt : bool) (d : nat) (name : PrimString.string)
    (acc : list PrimString.string) : list PrimString.string :=
  let acc := emit name acc in
  if alt then emit (ind (S d)) (emit nl (emit " {" acc))
  else emit " { " acc.

Definition sclose (alt : bool) (d : nat) (acc : list PrimString.string)
    : list PrimString.string :=
  if alt then emit "}" (emit (ind d) (emit nl (emit "," acc)))
  else emit " }" acc.

(** List printer over an entry emitter (the entry emitter is built at
    depth [S d] by the caller). *)
Definition pp_list_go {A : Type} (alt : bool) (d : nat)
    (pp_entry : A -> list PrimString.string -> list PrimString.string)
    (entries : list A) (acc : list PrimString.string)
    : list PrimString.string :=
  match entries with
  | [] => emit "[]" acc
  | e :: rest =>
      let acc := copen alt d "[" acc in
      let acc := pp_entry e acc in
      let acc :=
        List.fold_left (fun acc e => pp_entry e (csep alt d acc)) rest acc in
      cclose alt d "]" acc
  end.

(** ** Leaf renderings *)

(** Affine point: [(x, y)], inline in both forms (the impl writes
    directly).  All 44 pinned commitments are non-identity. *)
Definition pp_point (xy : Z * Z) (acc : list PrimString.string)
    : list PrimString.string :=
  let acc := emit "(" acc in
  let acc := emit (hex64 (fst xy)) acc in
  let acc := emit ", " acc in
  let acc := emit (hex64 (snd xy)) acc in
  emit ")" acc.

(** [Rotation(n)]: derived tuple struct over the signed decimal. *)
Definition pp_rotation (alt : bool) (d : nat) (r : Z)
    (acc : list PrimString.string) : list PrimString.string :=
  let acc := copen alt d "Rotation(" acc in
  let acc := emit (dec_Z r) acc in
  cclose alt d ")" acc.

(** [Column { index, column_type }] with the bare kind marker. *)
Definition pp_column (alt : bool) (d : nat) (kind : PrimString.string)
    (idx : Z) (acc : list PrimString.string) : list PrimString.string :=
  let acc := sopen alt d "Column" acc in
  let acc := emit "index: " acc in
  let acc := emit (dec_Z idx) acc in
  let acc := csep alt d acc in
  let acc := emit "column_type: " acc in
  let acc := emit kind acc in
  sclose alt d acc.

(** ** Query-index resolution

    The model carries no query indices; every query leaf resolves its
    [query_index] by position in the pinned keygen-order query table of its
    column kind ([compiled/pinned.v]; set-equal to the model's
    collected tables by the query parity certificates).  The same pinned
    tables are printed as the query sections, so the internal consistency
    of leaf indices and tables is forced by the byte parity. *)

Fixpoint index_of_go (q : Z * Z) (l : list (Z * Z)) (i : Z) : Z :=
  match l with
  | [] => -1
  | x :: rest => if Queries.query_eqb x q then i else index_of_go q rest (i + 1)
  end.

Definition advice_index (c r : Z) : Z :=
  index_of_go (c, r) OrchardCompiledPinned.advice_queries 0.

Definition fixed_index (c r : Z) : Z :=
  index_of_go (c, r) OrchardCompiledPinned.fixed_queries 0.

Definition instance_index (c r : Z) : Z :=
  index_of_go (c, r) OrchardCompiledPinned.instance_queries 0.

(** Query leaf: a struct with the field name [query_index] (the Rust field
    is [index]), then [column_index], then [rotation]. *)
Definition pp_query (alt : bool) (d : nat) (name : PrimString.string)
    (qi ci r : Z) (acc : list PrimString.string) : list PrimString.string :=
  let acc := sopen alt d name acc in
  let acc := emit "query_index: " acc in
  let acc := emit (dec_Z qi) acc in
  let acc := csep alt d acc in
  let acc := emit "column_index: " acc in
  let acc := emit (dec_Z ci) acc in
  let acc := csep alt d acc in
  let acc := emit "rotation: " acc in
  let acc := pp_rotation alt (S d) r acc in
  sclose alt d acc.

(** ** Expressions *)

Definition pallas_p : Z := Primes.pallas_p.

Fixpoint pp_expr (alt : bool) (d : nat)
    (e : Expression.t Configure.indexed_columns)
    (acc : list PrimString.string) {struct e} : list PrimString.string :=
  match e with
  | Expression.Constant z =>
      let acc := copen alt d "Constant(" acc in
      let acc := emit (hex64 (z mod pallas_p)) acc in
      cclose alt d ")" acc
  | Expression.Selector s =>
      (* Unreachable on the compiled system ([compiled_selector_free]);
         rendered as the source tuple struct for totality. *)
      let acc := copen alt d "Selector(" acc in
      let acc := emit (dec_Z s) acc in
      cclose alt d ")" acc
  | Expression.Fixed c r =>
      pp_query alt d "Fixed" (fixed_index c r.(Rotation.offset)) c
        r.(Rotation.offset) acc
  | Expression.Advice c r =>
      pp_query alt d "Advice" (advice_index c r.(Rotation.offset)) c
        r.(Rotation.offset) acc
  | Expression.Instance_ c r =>
      pp_query alt d "Instance" (instance_index c r.(Rotation.offset)) c
        r.(Rotation.offset) acc
  | Expression.Negated x =>
      let acc := copen alt d "Negated(" acc in
      let acc := pp_expr alt (S d) x acc in
      cclose alt d ")" acc
  | Expression.Sum a b =>
      let acc := copen alt d "Sum(" acc in
      let acc := pp_expr alt (S d) a acc in
      let acc := csep alt d acc in
      let acc := pp_expr alt (S d) b acc in
      cclose alt d ")" acc
  | Expression.Product a b =>
      let acc := copen alt d "Product(" acc in
      let acc := pp_expr alt (S d) a acc in
      let acc := csep alt d acc in
      let acc := pp_expr alt (S d) b acc in
      cclose alt d ")" acc
  | Expression.Scaled x z =>
      let acc := copen alt d "Scaled(" acc in
      let acc := pp_expr alt (S d) x acc in
      let acc := csep alt d acc in
      let acc := emit (hex64 (z mod pallas_p)) acc in
      cclose alt d ")" acc
  end.

(** ** The printed gate list

    The deployed gate builder's product chains are applications of Rust's
    left-associative [*]; the model's [constraint_to_expression] groups the
    same factor sequence differently on two gates (indices 6 and 7, the
    curve-equation checks), whose top-level product is rotated one step
    here to the deployed association.  [gate_polynomials_match]
    ([compiled/check.v]) compares gates by flattened factor
    fingerprint precisely because of this re-association;
    [printed_gates_gate_fp] below proves the rotation preserves those
    fingerprints, so the printed gates are the parity-certified
    polynomials. *)

Definition rotate_top (e : Expression.t Configure.indexed_columns)
    : Expression.t Configure.indexed_columns :=
  match e with
  | Expression.Product l (Expression.Product a b) =>
      Expression.Product (Expression.Product l a) b
  | _ => e
  end.

Definition assoc_fixed_gate
    (ig : nat * Expression.t Configure.indexed_columns)
    : Expression.t Configure.indexed_columns :=
  let '(i, g) := ig in
  if orb (Nat.eqb i 6) (Nat.eqb i 7) then rotate_top g else g.

Definition printed_gates : list (Expression.t Configure.indexed_columns) :=
  List.map assoc_fixed_gate
    (List.combine
      (List.seq 0
        (List.length
          OrchardCompiledCheck.compiled.(CompiledSystem.gates)))
      OrchardCompiledCheck.compiled.(CompiledSystem.gates)).

Lemma rotate_top_gate_fp (e : Expression.t Configure.indexed_columns) :
  OrchardCompiledCheck.gate_fp (rotate_top e)
  = OrchardCompiledCheck.gate_fp e.
Proof.
  destruct e; try reflexivity.
  destruct e2; try reflexivity.
  unfold OrchardCompiledCheck.gate_fp; cbn [OrchardCompiledCheck.factors].
  now rewrite List.app_assoc.
Qed.

Lemma map_assoc_fixed_gate_fp
    (s : list nat) (l : list (Expression.t Configure.indexed_columns)) :
  List.length s = List.length l ->
  List.map OrchardCompiledCheck.gate_fp
    (List.map assoc_fixed_gate (List.combine s l))
  = List.map OrchardCompiledCheck.gate_fp l.
Proof.
  revert s; induction l as [| g l IH]; intros s Hlen;
    destruct s as [| i s]; simpl in *; try reflexivity; try discriminate.
  f_equal.
  - unfold assoc_fixed_gate.
    destruct (orb (Nat.eqb i 6) (Nat.eqb i 7));
      [apply rotate_top_gate_fp | reflexivity].
  - apply IH; congruence.
Qed.

(** The printed gates carry exactly the parity-certified fingerprints. *)
Lemma printed_gates_gate_fp :
  List.map OrchardCompiledCheck.gate_fp printed_gates
  = List.map OrchardCompiledCheck.gate_fp
      OrchardCompiledCheck.compiled.(CompiledSystem.gates).
Proof.
  apply map_assoc_fixed_gate_fp.
  apply List.length_seq.
Qed.

(** ** Sections of the description *)

(** Query-table entry: the tuple [(Column { .. }, Rotation(..))]. *)
Definition pp_query_entry (alt : bool) (d : nat) (kind : PrimString.string)
    (cr : Z * Z) (acc : list PrimString.string) : list PrimString.string :=
  let acc := copen alt d "(" acc in
  let acc := pp_column alt (S d) kind (fst cr) acc in
  let acc := csep alt d acc in
  let acc := pp_rotation alt (S d) (snd cr) acc in
  cclose alt d ")" acc.

Definition pp_queries (alt : bool) (d : nat) (kind : PrimString.string)
    (qs : list (Z * Z)) (acc : list PrimString.string)
    : list PrimString.string :=
  pp_list_go alt d (pp_query_entry alt (S d) kind) qs acc.

Definition kind_name (k : Raw.ColumnKind.t) : PrimString.string :=
  match k with
  | Raw.ColumnKind.Advice => "Advice"
  | Raw.ColumnKind.Fixed => "Fixed"
  | Raw.ColumnKind.Instance_ => "Instance"
  end.

Definition pp_colref (alt : bool) (d : nat) (c : Raw.ColumnRef.t)
    (acc : list PrimString.string) : list PrimString.string :=
  pp_column alt d (kind_name c.(Raw.ColumnRef.kind))
    c.(Raw.ColumnRef.index) acc.

(** [permutation::Argument { columns }]. *)
Definition pp_permutation_argument (alt : bool) (d : nat)
    (acc : list PrimString.string) : list PrimString.string :=
  let acc := sopen alt d "Argument" acc in
  let acc := emit "columns: " acc in
  let acc :=
    pp_list_go alt (S d) (pp_colref alt (S (S d)))
      OrchardCompiledCheck.compiled.(CompiledSystem.permutation_columns)
      acc in
  sclose alt d acc.

(** [lookup::Argument { input_expressions, table_expressions }].  Inputs
    are the compiled (selector-substituted) input expressions; the table
    side of each pair is its fixed column, queried at the current rotation
    (the identity correspondence certified by [lookup_tables_match]). *)
Definition pp_lookup_argument (alt : bool) (d : nat)
    (lk : LookupArgument.t Configure.indexed_columns)
    (acc : list PrimString.string) : list PrimString.string :=
  let acc := sopen alt d "Argument" acc in
  let acc := emit "input_expressions: " acc in
  let acc :=
    pp_list_go alt (S d)
      (fun pair acc => pp_expr alt (S (S d)) (fst pair) acc)
      lk.(LookupArgument.pairs) acc in
  let acc := csep alt d acc in
  let acc := emit "table_expressions: " acc in
  let acc :=
    pp_list_go alt (S d)
      (fun pair acc =>
        pp_query alt (S (S d)) "Fixed"
          (fixed_index (OrchardCompiledCheck.table_fixed_column (snd pair)) 0)
          (OrchardCompiledCheck.table_fixed_column (snd pair)) 0 acc)
      lk.(LookupArgument.pairs) acc in
  sclose alt d acc.

Definition pp_option_Z (alt : bool) (d : nat) (o : option Z)
    (acc : list PrimString.string) : list PrimString.string :=
  match o with
  | None => emit "None" acc
  | Some n =>
      let acc := copen alt d "Some(" acc in
      let acc := emit (dec_Z n) acc in
      cclose alt d ")" acc
  end.

(** [PinnedEvaluationDomain { k, extended_k, omega }]. *)
Definition pp_domain (alt : bool) (d : nat) (acc : list PrimString.string)
    : list PrimString.string :=
  let acc := sopen alt d "PinnedEvaluationDomain" acc in
  let acc := emit "k: " acc in
  let acc := emit (dec_Z (Z.of_nat PolyDomain.k)) acc in
  let acc := csep alt d acc in
  let acc := emit "extended_k: " acc in
  let acc := emit (dec_Z VkPinnedData.extended_k) acc in
  let acc := csep alt d acc in
  let acc := emit "omega: " acc in
  let acc := emit (hex64 PolyDomain.omega) acc in
  sclose alt d acc.

(** [PinnedConstraintSystem], fields in declaration order. *)
Definition pp_cs (alt : bool) (d : nat) (acc : list PrimString.string)
    : list PrimString.string :=
  let acc := sopen alt d "PinnedConstraintSystem" acc in
  let acc := emit "num_fixed_columns: " acc in
  let acc := emit (dec_Z OrchardCompiledPinned.num_fixed_columns) acc in
  let acc := csep alt d acc in
  let acc := emit "num_advice_columns: " acc in
  let acc := emit (dec_Z OrchardCompiledPinned.num_advice_columns) acc in
  let acc := csep alt d acc in
  let acc := emit "num_instance_columns: " acc in
  let acc := emit (dec_Z OrchardCompiledPinned.num_instance_columns) acc in
  let acc := csep alt d acc in
  let acc := emit "num_selectors: " acc in
  let acc := emit (dec_Z OrchardCompiledPinned.num_selectors) acc in
  let acc := csep alt d acc in
  let acc := emit "gates: " acc in
  let acc :=
    pp_list_go alt (S d) (pp_expr alt (S (S d))) printed_gates acc in
  let acc := csep alt d acc in
  let acc := emit "advice_queries: " acc in
  let acc :=
    pp_queries alt (S d) "Advice" OrchardCompiledPinned.advice_queries acc in
  let acc := csep alt d acc in
  let acc := emit "instance_queries: " acc in
  let acc :=
    pp_queries alt (S d) "Instance" OrchardCompiledPinned.instance_queries
      acc in
  let acc := csep alt d acc in
  let acc := emit "fixed_queries: " acc in
  let acc :=
    pp_queries alt (S d) "Fixed" OrchardCompiledPinned.fixed_queries acc in
  let acc := csep alt d acc in
  let acc := emit "permutation: " acc in
  let acc := pp_permutation_argument alt (S d) acc in
  let acc := csep alt d acc in
  let acc := emit "lookups: " acc in
  let acc :=
    pp_list_go alt (S d) (pp_lookup_argument alt (S (S d)))
      OrchardCompiledCheck.compiled.(CompiledSystem.lookups) acc in
  let acc := csep alt d acc in
  let acc := emit "constants: " acc in
  let acc :=
    pp_list_go alt (S d)
      (fun c acc => pp_column alt (S (S d)) "Fixed" c acc)
      OrchardCompiledCheck.compiled.(CompiledSystem.constants) acc in
  let acc := csep alt d acc in
  let acc := emit "minimum_degree: " acc in
  let acc := pp_option_Z alt (S d) VkPinnedData.minimum_degree acc in
  sclose alt d acc.

(** [PinnedVerificationKey], fields in declaration order. *)
Definition pp_vk_fields (alt : bool) (acc : list PrimString.string)
    : list PrimString.string :=
  let acc := sopen alt 0 "PinnedVerificationKey" acc in
  let acc := emit "base_modulus: " acc in
  let acc := emit dquote acc in
  let acc := emit VkPinnedData.base_modulus acc in
  let acc := emit dquote acc in
  let acc := csep alt 0 acc in
  let acc := emit "scalar_modulus: " acc in
  let acc := emit dquote acc in
  let acc := emit VkPinnedData.scalar_modulus acc in
  let acc := emit dquote acc in
  let acc := csep alt 0 acc in
  let acc := emit "domain: " acc in
  let acc := pp_domain alt 1 acc in
  let acc := csep alt 0 acc in
  let acc := emit "cs: " acc in
  let acc := pp_cs alt 1 acc in
  let acc := csep alt 0 acc in
  let acc := emit "fixed_commitments: " acc in
  let acc :=
    pp_list_go alt 1 pp_point VkPinnedData.fixed_commitments acc in
  let acc := csep alt 0 acc in
  let acc := emit "permutation: " acc in
  let acc := sopen alt 1 "VerifyingKey" acc in
  let acc := emit "commitments: " acc in
  let acc :=
    pp_list_go alt 2 pp_point VkPinnedData.permutation_commitments acc in
  let acc := sclose alt 1 acc in
  sclose alt 0 acc.

(** The printer: [alt = true] is the pretty [{:#?}] rendering, [alt =
    false] the compact [{:?}] rendering.  The accumulator is reversed with
    the linear [rev_append] ([List.rev] is quadratic and dominates the
    whole computation on a 10^5-fragment list). *)
Definition pp_vk (alt : bool) : PrimString.string :=
  join (List.rev_append (pp_vk_fields alt []) []).

(** The pretty dump content: [format!("{:#?}\n", vk.pinned())] — the
    rendering plus one trailing newline.  T1 target. *)
Definition vk_pinned_pretty : PrimString.string :=
  PrimString.cat (pp_vk true) nl.

(** The compact string [s = format!("{:?}", vk.pinned())] — the exact
    input (after the [le64] length prefix) of the BLAKE2b-512
    [transcript_repr] hash.  T2 consumes this. *)
Definition vk_pinned_compact : PrimString.string :=
  pp_vk false.

(** ** Byte view (for the T2 hash input) *)

Definition byte_at (s : PrimString.string) (i : nat) : Z :=
  Uint63.to_Z (PrimString.get s (Uint63.of_Z (Z.of_nat i))).

Definition pstring_bytes (s : PrimString.string) : list Z :=
  List.map (byte_at s)
    (List.seq 0 (Z.to_nat (Uint63.to_Z (PrimString.length s)))).

Definition vk_pinned_compact_bytes : list Z :=
  pstring_bytes vk_pinned_compact.

End VkPinnedPrint.
