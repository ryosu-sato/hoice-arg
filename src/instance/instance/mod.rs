//! Actual instance structure.

use common::* ;
use instance::info::* ;
use learning::ice::quals::NuQuals ;
use data::Data ;

mod clause ;
mod pre_instance ;

pub use self::clause::Clause ;
pub use self::pre_instance::PreInstance ;




/// Stores the instance: the clauses, the factory and so on.
///
/// # NB
///
/// Clause indices can vary during instance building, because of the
/// simplifications that can remove clauses.
///
/// So, `pred_to_clauses` has to be carefully maintained, the easiest way to
/// do this is to never access an instance's fields directly from the outside.
#[derive(Clone)]
pub struct Instance {
  /// Predicates.
  preds: PrdInfos,
  /// Original predicates, for reconstruction.
  ///
  /// Stores the original signature of the predicates, and a map from the
  /// variables of `preds` to the original signature.
  old_preds: PrdMap< (Sig, VarMap<VarIdx>) >,
  /// Maps new variables to the new ones.
  ///
  /// Only available after finalize.
  old_var_maps: PrdMap<VarMap<Term>>,
  /// Predicates for which a suitable term has been found.
  pred_terms: PrdMap< Option< TTerms > >,

  /// Predicates defined in `pred_terms`, sorted by predicate dependencies.
  ///
  /// Populated by the `finalize` function.
  sorted_pred_terms: Vec<PrdIdx>,

  /// Clauses.
  clauses: ClsMap<Clause>,
  /// Maps predicates to the clauses where they appear in the lhs and rhs
  /// respectively.
  pred_to_clauses: PrdMap< (ClsSet, ClsSet) >,
  /// Unsat flag.
  is_unsat: bool,
  /// Set of positive clauses.
  ///
  /// Only available after finalize.
  pos_clauses: ClsSet,
  /// Set of strictly negative clauses.
  ///
  /// A clause is strictly negative if it has strictly one predicate
  /// application, and it's in the clause's body. Only available after
  /// finalize.
  strict_neg_clauses: ClsSet,
  /// Set of non-strictly negative clauses.
  ///
  /// A clause is strictly negative if it has strictly one predicate
  /// application, and it's in the clause's body. Only available after
  /// finalize.
  non_strict_neg_clauses: ClsSet,
  /// Set of (non-strictly) negative clauses.
  ///
  /// Super set of strictly negative clauses. Only available after finalize.
  neg_clauses: ClsSet,
  /// Set of implication clauses.
  ///
  /// Only available after finalize.
  imp_clauses: ClsSet,
  /// True if finalized already ran.
  is_finalized: bool,
  /// If this instance is the result of a split, contains the index of the
  /// clause of the original instance that the split was on.
  ///
  /// The constructor sets this to `None`. Function `clone_with_clauses`
  /// automatically sets it to the clause kept.
  split: Option<ClsIdx>,

  /// Define-funs parsed.
  define_funs: HashMap<String, (VarInfos, ::instance::parse::PTTerms)>,

  /// Maps **original** clause indexes to their optional name.
  old_names: ClsHMap<String>,

  /// Print success.
  ///
  /// Can only be set by `(set-option :print-success true)`.
  print_success: bool,
  /// Unsat core production.
  ///
  /// Can only be set by `(set-option :produce-unsat-cores true)`.
  unsat_cores: bool,
  /// Unsat core production.
  ///
  /// Can only be set by `(set-option :produce-proofs true)`.
  proofs: bool,
}
impl Instance {
  /// Instance constructor.
  pub fn new() -> Instance {
    let pred_capa = conf.instance.pred_capa ;
    let clause_capa = conf.instance.clause_capa ;
    Instance {
      preds: PrdMap::with_capacity(pred_capa),
      old_preds: PrdMap::with_capacity(pred_capa),
      old_var_maps: PrdMap::with_capacity(pred_capa),
      pred_terms: PrdMap::with_capacity(pred_capa),
      sorted_pred_terms: Vec::with_capacity(pred_capa),

      clauses: ClsMap::with_capacity(clause_capa),
      // clusters: CtrMap::with_capacity( clause_capa / 3 ),
      pred_to_clauses: PrdMap::with_capacity(pred_capa),
      is_unsat: false,
      pos_clauses: ClsSet::new(),
      strict_neg_clauses: ClsSet::new(),
      non_strict_neg_clauses: ClsSet::new(),
      neg_clauses: ClsSet::new(),
      imp_clauses: ClsSet::new(),
      is_finalized: false,
      split: None,
      define_funs: HashMap::new(),
      old_names: ClsHMap::with_capacity(clause_capa),
      print_success: false,
      unsat_cores: false,
      proofs: false,
    }
  }

  /// Clones itself.
  ///
  /// This is only used when splitting. `clause` will be remembered as the
  /// clause the split is on.
  ///
  /// Fails (in debug) if `clause` is not a negative clause of `self` or if
  /// `self` is not finalized.
  pub fn clone_with_clauses(& self, clause: ClsIdx) -> Self {
    debug_assert! { self.neg_clauses.contains(& clause) }
    debug_assert! { self.is_finalized }

    Instance {
      preds: self.preds.clone(),
      old_preds: self.old_preds.clone(),
      old_var_maps: PrdMap::with_capacity(self.old_preds.len()),
      pred_terms: self.pred_terms.clone(),
      sorted_pred_terms: Vec::with_capacity( self.preds.len() ),

      clauses: self.clauses.clone(),
      pred_to_clauses: self.pred_to_clauses.clone(),
      is_unsat: false,
      pos_clauses: ClsSet::new(),
      strict_neg_clauses: ClsSet::new(),
      non_strict_neg_clauses: ClsSet::new(),
      neg_clauses: ClsSet::new(),
      imp_clauses: ClsSet::new(),
      is_finalized: false,
      split: Some(clause),
      define_funs: self.define_funs.clone(),
      old_names: self.old_names.clone(),
      print_success: false,
      unsat_cores: false,
      proofs: false,
    }
  }

  /// Set of positive clauses.
  ///
  /// Only available after finalize.
  pub fn pos_clauses(& self) -> & ClsSet {
    & self.pos_clauses
  }
  /// Set of negative clauses with exactly one predicate application.
  ///
  /// Only available after finalize.
  pub fn strict_neg_clauses(& self) -> & ClsSet {
    & self.strict_neg_clauses
  }
  /// Set of negative clauses.
  ///
  /// Only available after finalize.
  pub fn neg_clauses(& self) -> & ClsSet {
    & self.neg_clauses
  }
  /// Set of non-strict negative clauses.
  ///
  /// Only available after finalize.
  pub fn non_strict_neg_clauses(& self) -> & ClsSet {
    & self.non_strict_neg_clauses
  }
  /// Set of implication clauses ad negative clausesh.
  ///
  /// Only available after finalize.
  pub fn imp_clauses(& self) -> & ClsSet {
    & self.imp_clauses
  }

  /// Number of active (not forced) predicates.
  pub fn active_pred_count(& self) -> usize {
    let mut count = 0 ;
    for pred in self.pred_indices() {
      if ! self.is_known(pred) { count += 1 }
    }
    count
  }

  /// Returns true if the instance is already solved.
  pub fn is_solved(& self) -> bool {
    if self.is_unsat { return true }
    for def in & self.pred_terms {
      if def.is_none() { return false }
    }
    true
  }

  /// Map from the original signature of a predicate.
  pub fn map_from_original_sig_of(
    & self, pred: PrdIdx
  ) -> VarHMap<Term> {
    let mut res = VarHMap::with_capacity( self.old_preds[pred].1.len() ) ;
    for (tgt, src) in self.old_preds[pred].1.index_iter() {
      res.insert(
        * src, term::var(tgt, self.old_preds[pred].0[* src].clone())
      ) ;
    }
    res
  }

  /// Original signature of a predicate.
  pub fn original_sig_of(& self, pred: PrdIdx) -> & Sig {
    & self.old_preds[pred].0
  }
  /// Map to the original signature of a predicate.
  pub fn map_to_original_sig_of(& self, pred: PrdIdx) -> & VarMap<VarIdx> {
    & self.old_preds[pred].1
  }

  /// If this instance is the result of a split, returns the index of the
  /// clause of the original instance that the split was on.
  ///
  /// Used mainly to create different folders for log files when splitting.
  pub fn split(& self) -> Option<ClsIdx> {
    self.split.clone()
  }

  /// True if the unsat flag is set.
  pub fn is_unsat(& self) -> bool {
    self.is_unsat
  }

  /// Sets the unsat flag in the instance.
  pub fn set_unsat(& mut self) {
    self.is_unsat = true
  }

  /// True if a predicate is forced to something.
  #[inline]
  pub fn is_known(& self, pred: PrdIdx) -> bool {
    self.pred_terms[pred].is_some()
  }

  /// Adds a define fun.
  pub fn add_define_fun<S: Into<String>>(
    & mut self, name: S, sig: VarInfos, body: ::instance::parse::PTTerms
  ) -> Option<(VarInfos, ::instance::parse::PTTerms)> {
    self.define_funs.insert(name.into(), (sig, body))
  }
  /// Retrieves a define fun.
  pub fn get_define_fun(
    & self, name: & str
  ) -> Option<& (VarInfos, ::instance::parse::PTTerms)> {
    self.define_funs.get(name)
  }

  /// Returns the model corresponding to the input predicates and the forced
  /// predicates.
  ///
  /// The model is sorted in topological order.
  pub fn model_of(& self, candidates: Candidates) -> Res<Model> {
    use std::iter::Extend ;

    let mut model = Model::with_capacity( self.preds.len() ) ;
    model.extend(
      candidates.into_index_iter().filter_map(
        |(pred, tterms_opt)| tterms_opt.map(
          |term| {
            let (term, _) = term.subst(& self.old_var_maps[pred]) ;
            (pred, TTerms::of_term(None, term))
          }
        )
      )
    ) ;

    for pred in & self.sorted_pred_terms {
      let pred = * pred ;
      if let Some(ref tterms) = self.pred_terms[pred] {
        model.push(
          (pred, tterms.subst(& self.old_var_maps[pred]))
        )
      } else {
        bail!("inconsistency in sorted forced predicates")
      }
    }

    Ok( model )
  }

  /// Returns the model corresponding to the input predicates and the forced
  /// predicates.
  ///
  /// The model is sorted in topological order.
  pub fn extend_model(& self, candidates: ConjCandidates) -> Res<ConjModel> {
    use std::iter::Extend ;
    let mut model = ConjModel::with_capacity( self.preds.len() ) ;
    let mut known_preds = PrdSet::new() ;
    let mut tmp: Vec<_> = candidates.into_iter().map(
      |(pred, conj)| {
        let mut preds = PrdSet::new() ;
        for tterms in & conj {
          preds.extend( tterms.preds() )
        }
        (pred, preds, conj)
      }
    ).collect() ;
    let mut cnt ;
    let mut changed ;
    while ! tmp.is_empty() {
      cnt = 0 ;
      changed = false ;
      while cnt < tmp.len() {
        if tmp[cnt].1.iter().all(
          |pred| known_preds.contains(pred)
        ) {
          changed = true ;
          let (pred, _, dnf) = tmp.swap_remove(cnt) ;
          let is_new = known_preds.insert(pred) ;
          debug_assert! { is_new }
          model.push( vec![ (pred, dnf) ] )
        } else {
          cnt += 1
        }
      }
      if ! changed {
        break
      }
    }
    if ! tmp.is_empty() {
      model.push(
        tmp.into_iter().map(
          |(pred, _, dnf)| (pred, dnf)
        ).collect()
      )
    }

    for pred in & self.sorted_pred_terms {
      let pred = * pred ;
      if let Some(ref tterms) = self.pred_terms[pred] {
        let tterms = tterms.subst(& self.old_var_maps[pred]) ;
        model.push(
          vec![ (pred, vec![ tterms ]) ]
        )
      } else {
        bail!("inconsistency in sorted forced predicates")
      }
    }
    Ok( model )
  }

  /// True if the instance is sat, false if unsat.
  fn is_trivial(& self) -> Option<bool> {
    if self.is_unsat {
      Some(false)
    } else if self.pred_terms.iter().all(|term| term.is_some()) {
      Some(true)
    } else {
      None
    }
  }

  /// Returns a model for the instance when all the predicates have terms
  /// assigned to them.
  pub fn is_trivial_conj(& self) -> Res< Option< Option<ConjModel> > > {
    match self.is_trivial() {
      None => Ok(None),
      Some(false) => Ok( Some(None) ),
      Some(true) => self.extend_model(
        PrdHMap::new()
      ).map(|res| Some(Some(res))),
    }
  }

  /// Returns a model for the instance when all the predicates have terms
  /// assigned to them.
  pub fn is_trivial_model(& self) -> Res< Option<Option<Model>> > {
    match self.is_trivial() {
      None => Ok(None),
      Some(false) => Ok( Some(None) ),
      Some(true) => self.model_of(
        PrdMap::new()
      ).map(|res| Some(Some(res))),
    }
  }


  /// Lhs and rhs predicates of a clause.
  #[inline]
  pub fn preds_of_clause(
    & self, clause: ClsIdx
  ) -> (& PredApps, Option<PrdIdx>) {
    (
      self[clause].lhs_preds(), self[clause].rhs().map(|(prd, _)| prd)
    )
  }


  /// Prints some top terms as a model.
  ///
  /// Meaning variables are printed with default printing: `<var_idx>` is
  /// printed as `v_<var_idx>`.
  pub fn print_tterms_as_model<W: Write>(
    & self, w: & mut W, tterms: & TTerms
  ) -> IoRes<()> {
    tterms.write(
      w, |w, var| var.default_write(w),
      |w, pred, args| {
        write!(w, "({}", self[pred]) ? ;
        let mut prev: VarIdx = 0.into() ;
        for (var, arg) in args.index_iter() {
          let old_var = self.old_preds[pred].1[var] ;
          for var in VarRange::new(prev, old_var) {
            write!(
              w, " {}", self.old_preds[pred].0[var].default_val()
            ) ?
          }
          prev = old_var ;
          prev.inc() ;
          write!(w, " {}", arg) ?
        }
        for var in VarRange::new(prev, self.old_preds[pred].0.next_index()) {
          write!(
            w, " {}", self.old_preds[pred].0[var].default_val()
          ) ?
        }
        write!(w, ")")
      }
    )
  }

  /// Finalizes instance creation.
  ///
  /// - shrinks all collections
  /// - sorts forced predicates by dependencies
  ///
  /// # TO DO
  ///
  /// - optimize sorting of forced preds by dependencies (low priority)
  pub fn finalize(& mut self) -> Res<()> {
    if self.is_finalized { return Ok(()) }
    self.is_finalized = true ;

    self.sorted_pred_terms.clear() ;
    self.preds.shrink_to_fit() ;
    self.old_preds.shrink_to_fit() ;
    self.pred_terms.shrink_to_fit() ;
    self.clauses.shrink_to_fit() ;

    let mut tmp: Vec< (PrdIdx, PrdSet) > = Vec::with_capacity(
      self.preds.len()
    ) ;

    for (idx, clause) in self.clauses.index_iter_mut() {
      if clause.rhs().is_none() {
        if clause.lhs_pred_apps_len() == 1 {
          let is_new = self.strict_neg_clauses.insert(idx) ;
          debug_assert! { is_new }
        } else {
          let is_new = self.non_strict_neg_clauses.insert(idx) ;
          debug_assert! { is_new }
        }
        let is_new = self.neg_clauses.insert(idx) ;
        debug_assert! { is_new }
      } else if clause.lhs_preds().is_empty() {
        if ! (
          self.is_unsat || clause.rhs().is_some()
        ) {
          bail!(
            "{}\nfound a clause with no predicate during finalization",
            clause.to_string_info(& self.preds).unwrap()
          )
        }
        let is_new = self.pos_clauses.insert(idx) ;
        debug_assert! { is_new }
      } else {
        let is_new = self.imp_clauses.insert(idx) ;
        debug_assert! { is_new }
      }
    }

    // Populate `tmp`.
    let mut known_preds = PrdSet::with_capacity( self.preds.len() ) ;

    for pred in self.pred_indices() {
      if let Some(ref tterms) = self.pred_terms[pred] {
        tmp.push( (pred, tterms.preds()) )
      } else {
        known_preds.insert(pred) ;
      }
    }
    // Sort by dependencies.
    while ! tmp.is_empty() {
      let mut cnt = 0 ; // Will use swap remove.
      'find_preds: while cnt < tmp.len() {
        for pred in & tmp[cnt].1 {
          if ! known_preds.contains(pred) {
            // Don't know this predicate, keep going in `tmp`.
            cnt += 1 ;
            continue 'find_preds
          }
        }
        // Reachable only we already have all of the current pred's
        // dependencies.
        let (pred, _) = tmp.swap_remove(cnt) ;
        self.sorted_pred_terms.push(pred) ;
        known_preds.insert(pred) ;
        () // No `cnt` increment after swap remove.
      }
    }

    for (pred, info) in self.preds.index_iter() {
      let mut map = VarMap::with_capacity( info.sig.len() ) ;
      for (var, typ) in info.sig.index_iter() {
        map.push(
          term::var(self.old_preds[pred].1[var], typ.clone())
        )
      }
      self.old_var_maps.push(map)
    }

    self.sorted_pred_terms.shrink_to_fit() ;

    // If there are no clusters just create one cluster per clause.
    // if self.clusters.is_empty() {
    //   log_info! { "instance has no clusters, creating single clause clusters" }
    //   for (idx, clause) in self.clauses.index_iter() {
    //     self.clusters.push( Cluster::of_clause(idx, clause) )
    //   }
    // }

    Ok(())
  }


  /// Returns the term we already know works for a predicate, if any.
  pub fn forced_terms_of(& self, pred: PrdIdx) -> Option<& TTerms> {
    self.pred_terms[pred].as_ref()
  }

  /// If the input predicate is forced to a constant boolean, returns its
  /// value.
  pub fn bool_value_of(& self, pred: PrdIdx) -> Option<bool> {
    self.forced_terms_of(pred).and_then(
      |terms| terms.bool()
    )
  }

  /// Forced predicates in topological order.
  #[inline]
  pub fn sorted_forced_terms(& self) -> & Vec<PrdIdx> {
    & self.sorted_pred_terms
  }

  /// Returns the clauses in which the predicate appears in the lhs and rhs
  /// respectively.
  #[inline]
  pub fn clauses_of(& self, pred: PrdIdx) -> (& ClsSet, & ClsSet) {
    (& self.pred_to_clauses[pred].0, & self.pred_to_clauses[pred].1)
  }
  /// Returns the clauses in which `pred` appears in the lhs.
  #[inline]
  pub fn lhs_clauses_of(& self, pred: PrdIdx) -> & ClsSet {
    & self.pred_to_clauses[pred].0
  }
  /// Returns the clauses in which `pred` appears in the rhs.
  #[inline]
  pub fn rhs_clauses_of(& self, pred: PrdIdx) -> & ClsSet {
    & self.pred_to_clauses[pred].1
  }

  /// Adds a predicate application to a clause's lhs.
  pub fn clause_add_lhs_pred(
    & mut self, clause: ClsIdx, pred: PrdIdx, args: VarMap<Term>
  ) {
    self.pred_to_clauses[pred].0.insert(clause) ;
    self.clauses[clause].insert_pred_app(
      pred, args.into()
    ) ;
  }

  /// Adds a term to a clause's lhs.
  pub fn clause_add_lhs_term(
    & mut self, clause: ClsIdx, term: Term
  ) {
    self.clauses[clause].insert_term(term) ;
  }

  /// Forces the rhs of a clause to a predicate application.
  pub fn clause_force_rhs(
    & mut self, clause: ClsIdx, pred: PrdIdx, args: VarMap<Term>
  ) -> Res<()> {
    self.pred_to_clauses[pred].1.insert(clause) ;
    self.clauses[clause].set_rhs(
      pred, args.into()
    )
  }

  /// Adds some terms to the lhs of a clause.
  ///
  /// Updates `pred_to_clauses`.
  pub fn clause_lhs_extend<I: IntoIterator<Item = TTerm>>(
    & mut self, clause_idx: ClsIdx, tterms: I
  ) {
    let clause = & mut self.clauses[clause_idx] ;
    for tterm in tterms.into_iter() {
      match tterm {
        TTerm::P { pred, args } => {
          self.pred_to_clauses[pred].0.insert(clause_idx) ;
          clause.insert_pred_app(pred, args) ;
        },
        TTerm::T(term) => {
          clause.insert_term(term) ;
        },
      }
    }
  }

  /// Replaces the rhs of a clause.
  ///
  /// Updates `pred_to_clauses` for the term it inserts but **not** the one it
  /// removes.
  pub fn clause_rhs_force(
    & mut self, clause_idx: ClsIdx, tterm: TTerm
  ) -> Res<()> {
    let clause = & mut self.clauses[clause_idx] ;
    match tterm {
      TTerm::P { pred, args } => {
        clause.set_rhs(pred, args) ? ;
        let is_new = self.pred_to_clauses[pred].1.insert(clause_idx) ;
        debug_assert!( is_new )
      },
      TTerm::T(term) => {
        if term.bool() != Some(false) {
          clause.insert_term( term::not(term) ) ;
        }
        clause.unset_rhs() ;
      },
    }
    Ok(())
  }

  // /// Set of int constants **appearing in the predicates**. If more constants
  // /// are created after the instance building step, they will not appear here.
  // pub fn consts(& self) -> & HConSet<Term> {
  //   & self.consts
  // }

  /// Range over the predicate indices.
  pub fn pred_indices(& self) -> PrdRange {
    PrdRange::zero_to( self.preds.len() )
  }
  /// Range over the clause indices.
  pub fn clause_indices(& self) -> ClsRange {
    ClsRange::zero_to( self.clauses.len() )
  }

  /// Predicate accessor.
  pub fn preds(& self) -> & PrdInfos {
    & self.preds
  }
  /// Clause accessor.
  pub fn clauses(& self) -> & ClsMap<Clause> {
    & self.clauses
  }

  /// Removes all predicate applications of some predicate in the lhs of a
  /// clause.
  fn rm_pred_apps_in_lhs(& mut self, pred: PrdIdx, clause: ClsIdx) {
    self.pred_to_clauses[pred].0.remove(& clause) ;
    let prev = self.clauses[clause].drop_lhs_pred(pred) ;
    debug_assert! { prev.is_none() }
  }


  /// Strengthens some predicate by some terms using the clauses lhs where the
  /// predicate appears.
  ///
  /// Returns the number of clauses created.
  ///
  /// Currently pseudo-inactive. Can only remove predicate applications if they
  /// are found to be trivial given the strengthening.
  ///
  /// For all clauses `c` where `pred` appears in the lhs, creates a new clause
  /// that is `c` with every application of `pred` replaced by `tterms`
  /// instantiated on `pred`'s application arguments.
  pub fn strengthen_in_lhs(
    & mut self, pred: PrdIdx, tterms: Vec<TTerm>
  ) -> Res<usize> {
    // let mut nu_clauses = Vec::with_capacity(
    //   self.pred_to_clauses[pred].0.len()
    // ) ;
    let mut nu_tterms = HashSet::with_capacity( 29 ) ;
    let mut pred_apps_to_rm = Vec::with_capacity(11) ;

    'clause_iter: for clause in & self.pred_to_clauses[pred].0 {
      // debug_assert!( nu_tterms.is_empty() ) ;
      nu_tterms.clear() ;

      log_debug!{ "  - #{}", clause }

      if let Some(argss) = self[* clause].lhs_preds().get(& pred) {

        log_debug!{ "    {} applications", argss.len() }
        for args in argss {
          'tterm_iter: for tterm in & tterms {
            let tterm = tterm.subst_total(args) ? ;
            if let Some(b) = tterm.bool() {
              if ! b {
                log_debug!{ "      new clause is trivial, skipping" }
                continue 'clause_iter
              }
            } else {
              match tterm {
                TTerm::T(ref term) if self[
                  * clause
                ].lhs_terms().contains(term) => continue 'tterm_iter,
                TTerm::P { ref pred, ref args } if self[
                  * clause
                ].lhs_preds().get(pred).map(
                  |argss| argss.contains(args)
                ).unwrap_or(false) => continue 'tterm_iter,
                _ => ()
              }
              log_debug!{ "    - {}", tterm }
              nu_tterms.insert( tterm ) ;
            }
          }
        }

      } else {
        bail!(
          "inconsistent instance state \
          (`pred_to_clauses` in `strengthen_in_lhs`)"
        )
      }

      if nu_tterms.is_empty() {
        log_debug!{
          "    no new terms, can remove applications of this predicate"
        }
        pred_apps_to_rm.push( (pred, * clause) )
      } else {
        // let mut nu_clause = self[* clause].clone() ;

        // for tterm in nu_tterms.drain() {
        //   nu_clause.lhs_insert(tterm) ;
        // }

        // let should_remove = self.simplifier.clause_propagate(
        //   & mut nu_clause
        // ) ? ;
        // if should_remove {
        //   log_info!{
        //     "    new clause is trivial after propagation"
        //   }
        // } else {
        //   nu_clauses.push(nu_clause)
        // }
      }

    }

    for (pred, clause) in pred_apps_to_rm {
      self.rm_pred_apps_in_lhs(pred, clause)
    }
    // let count = nu_clauses.len() ;
    // log_info!{ "    adding {} clauses", count }
    // for clause in nu_clauses { self.push_clause(clause) ? }
    self.check("after strengthening (lhs)") ? ;

    // Ok(count)
    Ok(0)
  }

  /// Pushes a new predicate and returns its index.
  pub fn push_pred(
    & mut self, name: String, sig: Sig
  ) -> PrdIdx {
    let idx = self.preds.next_index() ;
    let mut var_map = VarMap::with_capacity( sig.len() ) ;
    for (var, _) in sig.index_iter() {
      var_map.push(var)
    }
    self.old_preds.push(
      (sig.clone(), var_map)
    ) ;
    self.preds.push( PrdInfo {
      name, idx, sig
    } ) ;
    self.pred_terms.push(None) ;

    self.pred_to_clauses.push(
      ( ClsSet::with_capacity(17), ClsSet::with_capacity(17) )
    ) ;
    idx
  }

  /// Removes and returns the indices of the clauses `pred` appears in the lhs
  /// of from `self.pred_to_clauses`.
  fn unlink_pred_lhs<LHS>(& mut self, pred: PrdIdx, lhs: & mut LHS)
  where LHS: ::std::iter::Extend<ClsIdx> {
    lhs.extend( self.pred_to_clauses[pred].0.drain() )
  }

  /// Removes and returns the indices of the clauses `pred` appears in the rhs
  /// of from `self.pred_to_clauses`.
  fn unlink_pred_rhs<RHS>(& mut self, pred: PrdIdx, rhs: & mut RHS)
  where RHS: ::std::iter::Extend<ClsIdx> {
    rhs.extend( self.pred_to_clauses[pred].1.drain() )
  }

  /// Goes trough the predicates in `from`, and updates `pred_to_clauses` so
  /// that they point to `to` instead.
  fn relink_preds_to_clauses(
    & mut self, from: ClsIdx, to: ClsIdx
  ) -> Res<()> {
    for pred in self.clauses[from].lhs_preds().keys() {
      let pred = * pred ;
      let was_there = self.pred_to_clauses[pred].0.remove(& from) ;
      let _ = self.pred_to_clauses[pred].0.insert(to) ;
      debug_assert!(was_there)
    }
    if let Some((pred, _)) = self.clauses[from].rhs() {
      let was_there = self.pred_to_clauses[pred].1.remove(& from) ;
      let _ = self.pred_to_clauses[pred].1.insert(to) ;
      debug_assert!(was_there)
    }
    Ok(())
  }

  /// Forget some clauses.
  ///
  /// Duplicates are handled as if there was only one.
  pub fn forget_clauses(
    & mut self, clauses: & mut Vec<ClsIdx>
  ) -> Res<()> {
    // Forgetting is done by swap remove, we sort in DESCENDING order so that
    // indices always make sense.
    clauses.sort_unstable_by(
      |c_1, c_2| c_2.cmp(c_1)
    ) ;
    let mut prev = None ;
    for clause in clauses.drain(0..) {
      log_debug!{
        "    forgetting {}", self[clause].to_string_info(& self.preds) ?
      }
      if prev == Some(clause) { continue }
      prev = Some(clause) ;
      let _ = self.forget_clause(clause) ? ;
    }
    Ok(())
  }

  /// Forget a clause. **Does not preserve the order of the clauses.**
  ///
  /// After calling this function, clause indices kept outside of the instance
  /// will in general refer to clauses different from the ones they pointed to
  /// before the call.
  ///
  /// Also unlinks predicates from `pred_to_clauses`.
  pub fn forget_clause(& mut self, clause: ClsIdx) -> Res<Clause> {
    for pred in self.clauses[clause].lhs_preds().keys() {
      let pred = * pred ;
      let was_there = self.pred_to_clauses[pred].0.remove(& clause) ;
      debug_assert!(
        was_there || self.is_known(pred)
      )
    }
    if let Some((pred, _)) = self.clauses[clause].rhs() {
      self.pred_to_clauses[pred].1.remove(& clause) ;
    }
    // Relink the last clause as its index is going to be `clause`. Except if
    // `clause` is already the last one.
    let last_clause: ClsIdx = ( self.clauses.len() - 1 ).into() ;
    if clause != last_clause {
      self.relink_preds_to_clauses(last_clause, clause) ?
    }
    let res = self.clauses.swap_remove(clause) ;
    Ok(res)
  }

  /// First free clause index.
  pub fn next_clause_index(& self) -> ClsIdx {
    self.clauses.next_index()
  }

  /// Pushes a new clause.
  pub fn push_new_clause(
    & mut self, vars: VarInfos, lhs: Vec<TTerm>, rhs: Option<PredApp>,
    info: & 'static str
  ) -> Res< Option<ClsIdx> > {
    let idx = self.clauses.next_index() ;
    let clause = clause::new(vars, lhs, rhs, info, idx) ;
    self.push_clause(clause)
  }

  /// The name of an original clause if any.
  pub fn name_of_old_clause(
    & self, cls: ClsIdx
  ) -> Option<& String> {
    self.old_names.get(& cls)
  }

  /// Sets the name for an original clause.
  pub fn set_old_clause_name(
    & mut self, cls: ClsIdx, name: String
  ) -> Res<()> {
    let prev = self.old_names.insert(cls, name) ;
    if let Some(prev) = prev {
      bail!(
        format!(
          "trying to name clause #{}, but it's already called {}", 
          cls, conf.bad(& prev)
        )
      )
    }
    Ok(())
  }

  /// Pushes a clause.
  ///
  /// Returns its index, if it was added.
  pub fn push_clause(& mut self, clause: Clause) -> Res< Option<ClsIdx> > {
    for term in clause.lhs_terms() {
      if let Some(false) = term.bool() {
        return Ok(None)
      }
    }
    let idx = self.clauses.next_index() ;
    let is_new = self.push_clause_unchecked(clause) ;
    // self.check("after `push_clause`") ? ;
    Ok( if is_new { Some(idx) } else { None } )
  }

  /// True if the clause is redundant.
  pub fn is_redundant(& self, idx: ClsIdx) -> bool {
    let clause = & self.clauses[idx] ;

    if let Some((pred, _)) = clause.rhs() {
      for i in & self.pred_to_clauses[pred].1 {
        if * i != idx && self[* i].same_as(& clause) {
          return true
        }
      }
    } else if let Some((pred, _)) = clause.lhs_preds().iter().next() {
      for i in & self.pred_to_clauses[* pred].0 {
        if * i != idx && self[* i].same_as(& clause) {
          return true
        }
      }
    } else {
      for (i, c) in self.clauses.index_iter() {
        if i != idx && c.same_as(& clause) { return true }
      }
    }
    false
  }

  /// Pushes a new clause, does not sanity-check but redundancy-checks.
  fn push_clause_unchecked(& mut self, clause: Clause) -> bool {
    let clause_index = self.clauses.next_index() ;
    self.clauses.push(clause) ;

    if self.is_redundant(clause_index) {
      self.clauses.pop() ;
      return false
    }

    for pred in self.clauses[clause_index].lhs_preds().keys() {
      let pred = * pred ;
      let is_new = self.pred_to_clauses[pred].0.insert(clause_index) ;
      debug_assert!(is_new)
    }
    if let Some((pred, _)) = self.clauses[clause_index].rhs() {
      let is_new = self.pred_to_clauses[pred].1.insert(clause_index) ;
      debug_assert!(is_new)
    }
    true
  }

  // /// Pushes a new clause and links, no redundancy check.
  // fn push_clause_raw(& mut self, clause: Clause) -> bool {
  //   let clause_index = self.clauses.next_index() ;
  //   self.clauses.push(clause) ;

  //   for pred in self.clauses[clause_index].lhs_preds().keys() {
  //     let pred = * pred ;
  //     let is_new = self.pred_to_clauses[pred].0.insert(clause_index) ;
  //     debug_assert!(is_new)
  //   }
  //   if let Some((pred, _)) = self.clauses[clause_index].rhs() {
  //     let is_new = self.pred_to_clauses[pred].1.insert(clause_index) ;
  //     debug_assert!(is_new)
  //   }
  //   true
  // }

  /// Extracts some qualifiers from all clauses.
  pub fn qualifiers(& self, quals: & mut NuQuals) -> Res<()> {
    for clause in & self.clauses {
      self.qualifiers_of_clause(clause, quals) ?
    }
    // Add boolean qualifiers for all predicate's bool vars.
    for pred in & self.preds {
      for (var, typ) in pred.sig.index_iter() {
        let mut bool_vars = Vec::new() ;
        if * typ == typ::bool() {
          let var = term::var(var, typ::bool()) ;
          quals.insert( var.clone(), pred.idx ) ? ;
          bool_vars.push(var)
        }
        if bool_vars.len() > 1 {
          quals.insert( term::and( bool_vars.clone() ), pred.idx ) ? ;
          quals.insert( term::or( bool_vars ), pred.idx ) ? ;
          ()
        }
      }
    }
    Ok(())
  }

  /// Extracts some qualifiers from a clause.
  ///
  /// # TO DO
  ///
  /// - write an explanation of what actually happens
  /// - and some tests, probably
  pub fn qualifiers_of_clause(
    & self, clause: & Clause, quals: & mut NuQuals
  ) -> Res<()> {
    // if clause.from_unrolling { return Ok(()) }

    let build_conj = self.clauses.len() < 2000 && conf.ice.mine_conjs ;

    // Variable to term maps, based on the way the predicates are used.
    let mut maps = vec![] ;

    scoped! {
      // Represents equalities between *pred vars* and terms over *clause
      // variables*. These will be added to `app_quals` if the total
      // substitution of the term by `map` succeeds.
      let mut eq_quals = VarHMap::with_capacity(7) ;

      clause.all_pred_apps_do(
        |pred, args| {
          debug_assert!( eq_quals.is_empty() ) ;

          // Qualifiers generated while looking at predicate applications.
          let mut app_quals: HConSet<Term> = HConSet::with_capacity(17) ;

          // All the *clause var* to *pred var* maps for this predicate
          // application.
          let mut map: VarHMap<Term> = VarHMap::with_capacity( args.len() ) ;

          for (pred_var, term) in args.index_iter() {
            let pred_var_typ = self[pred].sig[pred_var].clone() ;
            // Parameter's a variable?
            if let Some(clause_var_index) = term.var_idx() {

              // Clause variable's already known as parameter?
              if let Some(other_pred_var) = map.get(& clause_var_index).map(
                |t| t.clone()
              ) {
                // Equality qualifier.
                app_quals.insert(
                  term::eq(
                    term::var(pred_var, pred_var_typ), other_pred_var.clone()
                  )
                ) ;
              } else {
                // Add to map.
                let _prev = map.insert(
                  clause_var_index, term::var(pred_var, pred_var_typ)
                ) ;
                debug_assert!( _prev.is_none() )
              }

            } else {
              // Parameter's not a variable, store potential equality.
              let _prev = eq_quals.insert(
                pred_var, (pred_var_typ.clone(), term.clone())
              ) ;
              debug_assert!( _prev.is_none() ) ;
              // Try to revert the term.
              if let Some((var, term)) = term.invert_var(
                pred_var, pred_var_typ
              ) {
                if ! map.contains_key(& var) {
                  map.insert(var, term) ;
                } else if let Some(other_pred_var) = map.get(& var) {
                  app_quals.insert(
                    term::eq( other_pred_var.clone(), term )
                  ) ;
                  ()
                }
              }
            }

          }

          for (pred_var, (typ, term)) in eq_quals.drain() {
            if let Some((term, _)) = term.subst_total(& map) {
              app_quals.insert(
                term::eq( term::var(pred_var, typ), term )
              ) ;
            }
          }

          if ! app_quals.is_empty() {
            let build_conj = app_quals.len() > 1 ;
            let mut conj = Vec::with_capacity( app_quals.len() ) ;

            for term in & app_quals {
              if build_conj { conj.push(term.clone()) }
              quals.insert(term.clone(), pred) ? ;
            }

            if build_conj {
              let term = term::and(conj) ;
              quals.insert(term, pred) ? ;
              ()
            }
          }

          maps.push((pred, map, app_quals)) ;
          Ok(())
        }
      ) ?
    }

    // Stores the subterms of `lhs_terms`.
    let mut subterms = Vec::with_capacity(7) ;
    // Stores all (sub-)terms.
    let mut all_terms = HConSet::<Term>::with_capacity(
      clause.lhs_terms().len()
    ) ;
    // Stores all top terms.
    let mut conj = HConSet::<Term>::with_capacity(
      clause.lhs_terms().len()
    ) ;

    // Now look for atoms and try to apply the mappings above.
    for (pred, map, app_quals) in maps {
      all_terms.clear() ;
      conj.clear() ;
      debug_assert! { all_terms.is_empty() }
      debug_assert! { conj.is_empty() }

      for term in clause.lhs_terms().iter() {

        if let Some( (term, true) ) = term.subst_total(& map) {
          all_terms.insert(term.clone()) ;

          conj.insert( term.clone() ) ;

          let term = if let Some(term) = term.rm_neg() {
            term
          } else { term } ;

          quals.insert(term, pred) ? ;

          ()
        }

        debug_assert!( subterms.is_empty() ) ;
        subterms.push(term) ;

        while let Some(subterm) = subterms.pop() {
          match subterm.app_inspect() {
            Some( (Op::Or, terms) ) |
            Some( (Op::And, terms) ) |
            Some( (Op::Not, terms) ) |
            Some( (Op::Impl, terms) ) => for term in terms {
              subterms.push(term) ;
              if let Some( (qual, true) ) = term.subst_total(& map) {
                let qual = if let Some(qual) = qual.rm_neg() {
                  qual
                } else {
                  qual
                } ;
                quals.insert(qual, pred) ? ;
              }
            },
            _ => if let Some( (qual, true) ) = subterm.subst_total(& map) {
              all_terms.insert(qual) ;
            },
          }
        }

      }

      if build_conj {
        quals.insert(
          term::and(
            app_quals.iter().map(|t| t.clone()).collect()
          ), pred
        ) ? ;
        if conj.len() > 1 {
          quals.insert(
            term::and( conj.iter().map(|t| t.clone()).collect() ), pred
          ) ? ;
          quals.insert(
            term::and( conj.drain().chain(app_quals).collect() ), pred
          ) ? ;
        }
      }

      let mut all_terms = all_terms.iter() ;

      while let Some(term) = all_terms.next() {

        for other in all_terms.clone() {

          match (term.app_inspect(), other.app_inspect()) {

            (
              Some((op_1 @ Op::Ge, term_args)),
              Some((op_2 @ Op::Gt, other_args))
            ) |
            (
              Some((op_1 @ Op::Gt, term_args)),
              Some((op_2 @ Op::Ge, other_args))
            ) |
            (
              Some((op_1 @ Op::Gt, term_args)),
              Some((op_2 @ Op::Gt, other_args))
            ) |
            (
              Some((op_1 @ Op::Ge, term_args)),
              Some((op_2 @ Op::Ge, other_args))
            ) |

            (
              Some((op_1 @ Op::Eql, term_args)),
              Some((op_2 @ Op::Gt, other_args))
            ) |
            (
              Some((op_1 @ Op::Gt, term_args)),
              Some((op_2 @ Op::Eql, other_args))
            ) |

            (
              Some((op_1 @ Op::Ge, term_args)),
              Some((op_2 @ Op::Eql, other_args))
            ) |
            (
              Some((op_1 @ Op::Eql, term_args)),
              Some((op_2 @ Op::Ge, other_args))
            ) |

            (
              Some((op_1 @ Op::Eql, term_args)),
              Some((op_2 @ Op::Eql, other_args))
            ) => {

              if term_args[0].typ().is_arith()
              && term_args[0].typ() == other_args[0].typ() {
                let nu_lhs = term::add(
                  vec![ term_args[0].clone(), other_args[0].clone() ]
                ) ;

                let mut old_vars_1 = term::vars(& term_args[0]) ;
                let mut old_vars_2 = term::vars(& other_args[0]) ;
                let mut nu_vars = term::vars(& nu_lhs) ;

                let use_qual = self.clauses.len() < 35 || (
                  nu_vars.len() <= 2
                ) || (
                  nu_vars.len() < old_vars_1.len() + old_vars_2.len()
                ) ;

                if use_qual {
                  log! { @4
                    "from {}", term ;
                    "     {}", other
                  }
                } else {
                  // log! { @1
                  //   " " ;
                  //   "skipping" ;
                  //   "from {}", term ;
                  //   "     {}", other ;
                  //   "  -> {}", nu_lhs
                  // }
                }

                if use_qual {
                  let op = match (op_1, op_2) {
                    (_, Op::Gt) |
                    (Op::Gt, _) => Op::Gt,

                    (_, Op::Ge) |
                    (Op::Ge, _) => Op::Ge,

                    (Op::Eql, Op::Eql) => Op::Eql,

                    _ => unreachable!(),
                  } ;

                  let nu_term = term::app(
                    op, vec![
                      nu_lhs, term::add(
                        vec![
                          term_args[1].clone(), other_args[1].clone()
                        ]
                      )
                    ]
                  ) ;
                  quals.insert(nu_term.clone(), pred) ? ;

                  log! { @4 "  -> {}", nu_term }

                  if op_1 == Op::Eql {
                    let nu_lhs = term::sub(
                      vec![ other_args[0].clone(), term_args[0].clone() ]
                    ) ;
                    let nu_rhs = term::sub(
                      vec![ other_args[1].clone(), term_args[1].clone() ]
                    ) ;
                    let nu_term = term::app( op, vec![ nu_lhs, nu_rhs ] ) ;
                    quals.insert(nu_term, pred) ? ;
                  } else if op_2 == Op::Eql {
                    let nu_lhs = term::sub(
                      vec![ term_args[0].clone(), other_args[0].clone() ]
                    ) ;
                    let nu_rhs = term::sub(
                      vec![ term_args[1].clone(), other_args[1].clone() ]
                    ) ;
                    let nu_term = term::app( op, vec![ nu_lhs, nu_rhs ] ) ;
                    quals.insert(nu_term, pred) ? ;
                  }
                }
              }

            },

            _ => (),

          }

        }
      }
    }

    Ok(())

  }



  /// Transforms a cex for a clause into some learning data.
  ///
  /// Returns `true` if some new data was generated.
  pub fn clause_cex_to_data(
    & self, data: & mut Data, clause_idx: ClsIdx, cex: BCex
  ) -> Res<()> {
    let (mut cex, bias) = cex ;
    let clause = & self[clause_idx] ;

    if_log! { @6
      let mut s = String::new() ;
      for (var, val) in cex.index_iter() {
        s.push_str(& format!("{}: {}, ", var.default_str(), val))
      }
      log! { @6
        "lhs preds: {}", clause.lhs_pred_apps_len() ;
        "      rhs: {}", if clause.rhs().is_some() { "some" } else { "none" } ;
        "     bias: {}", bias ;
        "      cex: {}", s
      }
    }

    // Factored set of variables when fixing cex for arguments.
    let mut known_vars = VarSet::new() ;

    macro_rules! fix_cex {
      ($args:expr) => ({
        log! { @6 "fixing {}", $args }
        for arg in $args.iter() {
          for var in term::vars(arg) {
            if ! cex[var].is_known() {
              // Value for `var` is a non-value.
              let is_new = known_vars.insert(var) ;
              // Variable appears in more than one arg, force its value.
              if ! is_new {
                cex[var] = cex[var].typ().default_val()
              }
            }
          }
        }
      })
    }

    let (lhs, rhs) = match bias {

      // Consider the whole lhs of the clause positive.
      Bias::Lft => (vec![], clause.rhs()),

      // Consider the rhs of the clause negative.
      Bias::Rgt => (
        clause.lhs_preds().iter().map(
          |(pred, argss)| (* pred, argss.clone())
        ).collect(),
        None
      ),

      // Consider the rhs of the clause negative, and all lhs applications
      // positive except this one.
      Bias::NuRgt(pred, args) => {
        use var_to::terms::VarTermsSet ;
        debug_assert! { clause.lhs_preds().get(& pred).is_some() }
        debug_assert! {
          clause.lhs_preds().get(& pred).unwrap().contains(& args)
        }
        let mut argss = VarTermsSet::with_capacity(1) ;
        argss.insert(args) ;
        ( vec![(pred, argss)], None )
      },

      // No bias.
      Bias::Non => (
        clause.lhs_preds().iter().map(
          |(pred, argss)| (* pred, argss.clone())
        ).collect(),
        clause.rhs()
      ),

    } ;

    // Force non-values in the cex if we're dealing with a constraint, not a
    // sample.
    if (
      // Positive sample?
      lhs.is_empty() && rhs.is_some()
    ) || (
      // Negative sample?
      lhs.iter().next().map(
        |(_, argss)| argss.len() == 1
      ).unwrap_or(false) && rhs.is_none()
    ) {
      // We're generating a sample. Still need to force variables that appear
      // more than once in arguments.
      for (_, argss) in & lhs {
        debug_assert_eq! { argss.len(), 1 }
        for args in argss {
          fix_cex!(args)
        }
      }
      if let Some((_, args)) = rhs.as_ref() {
        fix_cex!(args)
      }
    } else {
      // We're dealing with a constraint, not a sample. Force non-values.
      for val in cex.iter_mut() {
        if ! val.is_known() {
          * val = val.typ().default_val()
        }
      }
    }

    // Evaluates some arguments for a predicate.
    macro_rules! eval {
      ($args:expr) => ({
        use var_to::vals::RVarVals ;
        let mut sample = RVarVals::with_capacity( $args.len() ) ;
        for arg in $args.get() {
          let val = arg.eval(& cex) ? ;
          sample.push(val)
        }
        sample
      }) ;
    }

    // Evaluate antecedents.
    let mut antecedents = vec![] ;
    for (pred, argss) in lhs {
      for args in argss {
        let sample = eval!(args) ;
        antecedents.push((pred, sample))
      }
    }

    let consequent = if let Some((pred, args)) = rhs {
      let sample = eval!(args) ;
      Some( (pred, sample) )
    } else {
      None
    } ;

    if_log! { @6
      let mut s = String::new() ;
      if ! antecedents.is_empty() {
        for (pred, sample) in & antecedents {
          s.push_str( & format!("({} {}) ", self[* pred], sample) )
        }
      } else {
        s.push_str("true ")
      }
      s.push_str("=> ") ;
      if let Some((pred, sample)) = consequent.as_ref() {
        s.push_str( & format!("({} {})", self[* pred], sample) )
      } else {
        s.push_str("false")
      }
      log! { @6 "{}", s }
    }

    data.add_data(clause_idx, antecedents, consequent)
  }




  /// Turns some teacher counterexamples into learning data.
  pub fn cexs_to_data(
    & self, data: & mut Data, cexs: Cexs
  ) -> Res<bool> {
    let metrics = data.metrics() ;

    for (clause_idx, cexs) in cexs.into_iter() {
      log! { @5 "adding cexs for #{}", clause_idx }

      for cex in cexs {
        self.clause_cex_to_data(data, clause_idx, cex) ?
      }
    }

    data.propagate() ? ;

    Ok( metrics != data.metrics() )
  }



  /// Checks that the instance has no inconsistencies.
  ///
  /// Only active in debug.
  #[cfg(not(debug_assertions))]
  #[inline(always)]
  pub fn check(& self, _: & 'static str) -> Res<()> { Ok(()) }

  #[cfg(debug_assertions)]
  pub fn check(& self, s: & 'static str) -> Res<()> {
    for clause in & self.clauses {
      clause.check(s) ?
    }
    self.check_pred_to_clauses().chain_err(
      || format!("while checking `{}`", conf.sad("pred_to_clauses"))
    ).chain_err(
      || format!("instance consistency check failed: {}", conf.emph(s))
    ) ? ;
    self.check_preds_consistency() ? ;
    
    for (idx, clause) in self.clauses.index_iter() {
      for term in clause.lhs_terms() {
        if let Some(false) = term.bool() {
          bail!(
            "({}) found a trivial clause: #{} {}", s, idx,
            clause.to_string_info(self.preds()).unwrap()
          )
        }
      }

      for pred in clause.lhs_preds().iter().map(
        |(pred, _)| * pred
      ).chain( clause.rhs().into_iter().map(|(pred, _)| pred) ) {
        if let Some(tterms) = self.forced_terms_of(pred) {
          bail! {
            "predicate {} is forced{} but appears in a clause: {}",
            conf.bad( & self[pred].name ),
            match tterms.bool() {
              Some(true) => " to true",
              Some(false) => " to false",
              None => "",
            },
            s
          }
        }
      }
    }

    scoped! {
      let mut clauses = self.clauses.iter() ;
      while let Some(clause) = clauses.next() {
        for c in clauses.clone() {
          if clause.same_as(c) {
            bail!(
              "{}\n\n{}\n\nsame clause appears multiple times\n{}",
              clause.to_string_info(self.preds()).unwrap(),
              c.to_string_info(self.preds()).unwrap(),
              conf.bad(s)
            )
          }
        }
      }
    }

    Ok(())
  }

  /// Checks `preds` and `old_preds` are consistent.
  #[cfg(debug_assertions)]
  fn check_preds_consistency(& self) -> Res<()> {
    for (pred, info) in self.preds.index_iter() {
      for (var, typ) in info.sig.index_iter() {
        let (ref old_sig, ref var_map) = self.old_preds[pred] ;
        if old_sig[ var_map[var] ] != * typ {
          bail!(
            "type inconsistency between current and original predicates:\n\
            on {}, variable {}: {} is routed to {}: {}",
            self[pred],
            var.default_str(), typ,
            var_map[var].default_str(), old_sig[ var_map[var] ]
          )
        }
      }
    }
    Ok(())
  }

  /// Pretty printer for a set of clauses.
  #[cfg(debug_assertions)]
  fn pretty_clauses(& self, clauses: & ClsSet) -> String {
    let mut s = String::new() ;
    s.push('{') ;
    for clause in clauses {
      s.push(' ') ;
      s.push_str(& format!("{}", clause))
    }
    s.push(' ') ;
    s.push('}') ;
    s
  }

  /// Checks the consistency of `pred_to_clauses`.
  #[cfg(debug_assertions)]
  fn check_pred_to_clauses(& self) -> Res<()> {
    for (cls_idx, clause) in self.clauses.index_iter() {
      for (pred, _) in clause.lhs_preds() {
        let pred = * pred ;
        if self.is_known(pred) {
          bail!(
            "predicate {} is forced but appears in lhs of clause {}",
            self[pred], cls_idx
          )
        }
        if ! self.pred_to_clauses[pred].0.contains(& cls_idx) {
          bail!(
            "predicate {} appears in lhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
      if let Some((pred, _)) = clause.rhs() {
        if self.is_known(pred) {
          bail!(
            "predicate {} is forced but appears in rhs of clause {}",
            self[pred], cls_idx
          )
        }
        if ! self.pred_to_clauses[pred].1.contains(& cls_idx) {
          bail!(
            "predicate {} appears in rhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
    }

    for (pred, & (ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
      'pred_clauses: for clause in lhs {
        if * clause >= self.clauses.len() {
          bail!(
            "predicate {} is registered as appearing in lhs of clause {} \
            which is above the maximal clause index", self[pred], clause
          )
        }
        if self.clauses[* clause].lhs_preds().get(& pred).is_none() {
          bail!(
            "predicate {} is registered as appearing in lhs of clause {} \
            but it's not the case\n{}\nlhs: {}\nrhs: {}",
            self[pred], clause,
            self.clauses[* clause].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
      for clause in rhs {
        if * clause >= self.clauses.len() {
          bail!(
            "predicate {} is registered as appearing in rhs of clause {} \
            which is above the maximal clause index", self[pred], clause
          )
        }
        if let Some((this_pred, _)) = self.clauses[* clause].rhs() {
          if this_pred == pred {
            continue
          }
        }
        bail!(
          "predicate {} is registered to appear in rhs of clause {} \
          but it's not the case\n{}\nlhs: {}\nrhs: {}",
          self[pred], clause,
          self.clauses[* clause].to_string_info(self.preds()) ?,
          self.pretty_clauses(
            & self.pred_to_clauses[pred].0
          ), self.pretty_clauses(
            & self.pred_to_clauses[pred].1
          )
        )
      }
    }
    Ok(())
  }


  /// Dumps the instance as an SMT-LIB 2 problem.
  pub fn dump_as_smt2<File, Blah>(
    & self, w: & mut File, blah: Blah
  ) -> Res<()>
  where File: Write, Blah: AsRef<str> {
    let blah = blah.as_ref() ;

    for line in blah.lines() {
      write!(w, "; {}\n", line) ?
    }
    write!(w, "\n") ? ;
    write!(w, "(set-logic HORN)\n\n") ? ;

    for (pred_idx, pred) in self.preds.index_iter() {
      if self.pred_terms[pred_idx].is_none() {
        write!(
          w, "({}\n  {}\n  (", keywords::cmd::dec_fun, pred.name
        ) ? ;
        for typ in & pred.sig {
          write!(w, " {}", typ) ?
        }
        write!(w, " ) Bool\n)\n") ?
      }
    }

    write!(
      w, "\n; Original clauses' names ({}) {{\n", self.old_names.len()
    ) ? ;
    for (idx, name) in & self.old_names {
      write!(w, ";   #{}: `{}`.\n", idx, name) ?
    }
    write!(w, "; }}\n") ? ;

    for (idx, clause) in self.clauses.index_iter() {
      write!(w, "\n; Clause #{}\n", idx) ? ;

      // Print source.
      let from = clause.from() ;
      write!(w, ";   from: #{}", from) ? ;
      if let Some(name) = self.old_names.get(& from) {
        write!(w, ": {}", name) ?
      }
      write!(w, "\n") ? ;

      clause.write(
        w, |w, p, args| {
          if ! args.is_empty() {
            write!(w, "(") ?
          }
          w.write_all( self[p].name.as_bytes() ) ? ;
          for arg in args.iter() {
            write!(w, " ") ? ;
            arg.write(w, |w, var| w.write_all( clause.vars[var].as_bytes() )) ?
          }
          if ! args.is_empty() {
            write!(w, ")")
          } else {
            Ok(())
          }
        }
      ) ? ;
      write!(w, "\n\n") ?
    }

    write!(w, "\n(check-sat)\n") ? ;

    Ok(())
  }


  /// Simplifies some predicate definitions.
  ///
  /// Simplifies its internal predicate definitions and the ones in the model.
  pub fn simplify_pred_defs(& mut self, model: & mut Model) -> Res<()> {
    let mut old_model = Vec::with_capacity( model.len() ) ;
    ::std::mem::swap( & mut old_model, model ) ;
    for (pred, def) in old_model {
      let simplified = def.simplify_pred_apps(& model, & self.pred_terms) ;
      model.push( (pred, simplified) )
    }

    if self.sorted_pred_terms.is_empty() {
      self.finalize() ?
    }

    let mut old_tterms: PrdMap<Option<TTerms>> = vec![
      None ; self.pred_terms.len()
    ].into() ;
    ::std::mem::swap( & mut old_tterms, & mut self.pred_terms ) ;
    for pred in & self.sorted_pred_terms {
      let mut curr_def = None ;
      ::std::mem::swap(& mut curr_def, & mut old_tterms[* pred]) ;
      if let Some(def) = curr_def {
        let simplified = def.simplify_pred_apps(& model, & self.pred_terms) ;
        self.pred_terms[* pred] = Some(simplified)
      }
    }
    Ok(())
  }


  /// Writes a conjunction of top terms.
  pub fn write_tterms_conj<W: Write>(
    & self, w: & mut W, conj: & Vec<TTerms>
  ) -> Res<()> {
    if conj.is_empty() {
      write!(w, "true") ?
    } else if conj.len() == 1 {
      self.print_tterms_as_model(w, & conj[0]) ?
    } else {
      write!(w, "(and") ? ;
      for tterms in conj {
        write!(w, " ") ? ;
        self.print_tterms_as_model(w, tterms) ?
      }
      write!(w, ")") ?
    }
    Ok(())
  }


  /// Writes a predicate signature.
  ///
  /// Does not write the name of the predicate.
  pub fn write_pred_sig<W: Write>(
    & self, w: & mut W, pred: PrdIdx
  ) -> Res<()> {
    let (ref old_sig, _) = self.old_preds[pred] ;
    write!(w, "(")  ?;
    for (var, typ) in old_sig.index_iter() {
      write!(w, " ({} {})", var.default_str(), typ) ?
    }
    write!(w, " ) {}", typ::bool()) ? ;
    Ok(())
  }



  /// Writes some definitions.
  pub fn write_definitions<W: Write>(
    & self, w: & mut W, pref: & str, model: & ConjModel
  ) -> Res<()> {

    for defs in model {

      if defs.is_empty() {
        ()
      } else if defs.len() == 1 {
        let (pred, ref tterms) = defs[0] ;

        writeln!(
          w, "{}({} {}", pref, keywords::cmd::def_fun, self[pred].name
        ) ? ;
        write!(w, "{}  ", pref)  ?;
        self.write_pred_sig(w, pred) ? ;
        write!(w, "\n{}  ", pref) ? ;
        self.write_tterms_conj(w, tterms) ? ;
        writeln!(w, "\n{})", pref) ?

      } else {
        write!(
          w, "{}({} (", pref, keywords::cmd::def_funs
        ) ? ;
        for & (pred, _) in defs {
          write!(w, "\n{}  {} ", pref, self[pred].name) ? ;
          self.write_pred_sig(w, pred) ? ;
        }
        write!(w, "\n{}) (", pref) ? ;
        for & (_, ref tterms) in defs {
          write!(w, "\n{}  ", pref) ? ;
          self.write_tterms_conj(w, tterms) ? ;
        }
        writeln!(w, "\n{}) )", pref) ? ;
      }
    }

    Ok(())
  }


  /// Writes a model.
  pub fn write_model<W: Write>(
    & self, model: & ConjModel, w: & mut W
  ) -> Res<()> {
    writeln!(w, "(model") ? ;
    self.write_definitions(w, "  ", model) ? ;
    writeln!(w, ")") ? ;
    Ok(())
  }




  /// Sets print-success flag.
  pub fn set_print_success(& mut self, b: bool) {
    self.print_success = b
  }
  /// Print-success flag accessor.
  pub fn print_success(& self) -> bool {
    self.print_success
  }
  /// Sets unsat-cores flag.
  pub fn set_unsat_cores(& mut self, b: bool) {
    self.unsat_cores = b
  }
  /// Unsat-cores flag.
  pub fn unsat_cores(& self) -> bool {
    self.unsat_cores
  }
  /// Sets proofs flag.
  pub fn set_proofs(& mut self, b: bool) {
    self.proofs = b
  }
  /// Unsat-cores flag.
  pub fn proofs(& self) -> bool {
    self.proofs
  }

  /// True if the teacher needs to maintain a sample graph (unsat
  /// cores/proofs).
  pub fn track_samples(& self) -> bool {
    self.unsat_cores() || self.proofs()
  }


  /// Converts `"true"` to `true`, `"false"` to `false`, and everything else to
  /// an error.
  fn bool_of_str(s: & str) -> Res<bool> {
    match s {
      "true" => Ok(true),
      "false" => Ok(false),
      _ => bail!("expected boolean `true/false`, got `{}`", s),
    }
  }
  


  /// Sets an option.
  pub fn set_option(& mut self, flag: & str, val: & str) -> Res<()> {
    let flag_err = || format!("while handling set-option for {}", flag) ;
    match flag {
      "print-success" => self.set_print_success(
        Self::bool_of_str(& val).chain_err(flag_err) ?
      ),
      "produce-unsat-cores" => self.set_unsat_cores(
        Self::bool_of_str(& val).chain_err(flag_err) ?
      ),
      "produce-proofs" => self.set_proofs(
        Self::bool_of_str(& val).chain_err(flag_err) ?
      ),
      _ => warn!(
        "ignoring (set-option :{} {}): unknown flag {}", flag, val, flag
      ),
    }
    Ok(())
  }



}
impl ::std::ops::Index<PrdIdx> for Instance {
  type Output = PrdInfo ;
  fn index(& self, index: PrdIdx) -> & PrdInfo {
    & self.preds[index]
  }
}
impl ::std::ops::Index<ClsIdx> for Instance {
  type Output = Clause ;
  fn index(& self, index: ClsIdx) -> & Clause {
    & self.clauses[index]
  }
}
impl ::std::ops::IndexMut<ClsIdx> for Instance {
  fn index_mut(& mut self, index: ClsIdx) -> & mut Clause {
    & mut self.clauses[index]
  }
}
impl AsRef<Instance> for Instance {
  fn as_ref(& self) -> & Self {
    self
  }
}
impl AsMut<Instance> for Instance {
  fn as_mut(& mut self) -> & mut Self {
    self
  }
}
// impl ::std::ops::Deref for Instance {
//   type Target = Self ;
//   fn deref(& self) -> & Self {
//     self
//   }
// }
// impl ::std::ops::DerefMut for Instance {
//   fn deref_mut(& mut self) -> & mut Self {
//     self
//   }
// }





impl<'a> PebcakFmt<'a> for Clause {
  type Info = & 'a PrdInfos ;
  fn pebcak_err(& self) -> ErrorKind {
    "during clause pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, prds: & 'a PrdInfos
  ) -> IoRes<()> {
    self.write(
      w, |w, prd, args| {
        write!(w, "(") ? ;
        w.write_all( prds[prd].as_bytes() ) ? ;
        for arg in args.iter() {
          write!(w, " ") ? ;
          arg.write(w, |w, var| w.write_all( self.vars[var].as_bytes() )) ?
        }
        write!(w, ")")
      }
    )
  }
}

impl<'a> PebcakFmt<'a> for Instance {
  type Info = () ;
  fn pebcak_err(& self) -> ErrorKind {
    "during instance pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, _: ()
  ) -> IoRes<()> {

    for (pred_idx, pred) in self.preds.index_iter() {
      if self.pred_terms[pred_idx].is_none() {
        write!(
          w, "({}\n  {}\n  (", keywords::cmd::dec_fun, pred.name
        ) ? ;
        for typ in & pred.sig {
          write!(w, " {}", typ) ?
        }
        write!(w, " ) Bool\n)\n") ? ;
        if pred.sig.len() != self.old_preds[pred_idx].0.len() {
          write!(w, "; original signature:\n;") ? ;
          for (var, typ) in self.old_preds[pred_idx].0.index_iter() {
            write!(
              w, " ({} {})", var.default_str(), typ
            ) ?
          }
          writeln!(w, "\n; variable map (new -> old):\n;") ? ;
          for (src, tgt) in self.old_preds[pred_idx].1.index_iter() {
            write!(
              w, " {} -> {},", src.default_str(), tgt.default_str()
            ) ?
          }
          writeln!(w, "") ?
        }
      }
    }

    use rsmt2::print::Expr2Smt ;
    let empty_prd_set = PrdSet::new() ;
    if self.sorted_pred_terms.is_empty() {
      // Either there's no forced predicate, or we are printing before
      // finalizing.
      for (pred, tterms) in self.pred_terms.index_iter().filter_map(
        |(pred, tterms_opt)| tterms_opt.as_ref().map(|tt| (pred, tt))
      ) {
        write!(w, "({} {}\n  (", keywords::cmd::def_fun, self[pred]) ? ;
        for (var, typ) in self[pred].sig.index_iter() {
          write!(w, " (v_{} {})", var, typ) ?
        }
        write!(w, " ) Bool\n  ") ? ;
        tterms.expr_to_smt2(
          w, & (& empty_prd_set, & empty_prd_set, & self.preds)
        ).unwrap() ;
        write!(w, "\n)\n") ?
      }
    } else {
      for pred in & self.sorted_pred_terms {
        write!(w, "({} {}\n  (", keywords::cmd::def_fun, self[* pred]) ? ;
        for (var, typ) in self[* pred].sig.index_iter() {
          write!(w, " (v_{} {})", var, typ) ?
        }
        let tterms = self.pred_terms[* pred].as_ref().unwrap() ;
        write!(w, " ) Bool\n  ") ? ;
        tterms.expr_to_smt2(
          w, & (& empty_prd_set, & empty_prd_set, & self.preds)
        ).unwrap() ;
        write!(w, "\n)\n", ) ?
      }
    }

    write!(
      w, "\n; Original clauses' names ({}) {{\n", self.old_names.len()
    ) ? ;
    for (idx, name) in & self.old_names {
      write!(w, "; Original clause #{} is called `{}`.\n", idx, name) ?
    }
    write!(w, "; }}\n") ? ;

    for (idx, clause) in self.clauses.index_iter() {
      write!(w, "\n; Clause #{}\n", idx) ? ;
      let from = clause.from() ;
      write!(w, ";   from: #{}", from) ? ;
      if let Some(name) = self.old_names.get(& from) {
        write!(w, ": {}", name) ?
      }
      write!(w, "\n") ? ;
      clause.pebcak_io_fmt(w, & self.preds) ?
    }

    write!(w, "\npred to clauses:\n") ? ;
    for (pred, & (ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
      write!(w, "  {}: lhs {{", self[pred]) ? ;
      for lhs in lhs {
        write!(w, " {}", lhs) ?
      }
      write!(w, " }}, rhs {{") ? ;
      for rhs in rhs {
        write!(w, " {}", rhs) ?
      }
      write!(w, " }}\n") ?
    }

    Ok(())
  }
}
