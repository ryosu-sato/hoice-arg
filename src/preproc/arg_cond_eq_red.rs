//!

use num::BigInt;
use std::vec;
use std::fs::File;
use std::io::{BufReader, Lines, prelude::*};
use std::path::Path;
use std::process::Command;
use std::time;

use crate::{
    common::{
        smt::{FullParser as Parser, SmtTerm},
        *,
    },
    data::Data,
    preproc::{PreInstance, RedStrat},
};


pub struct ArgCondEqRed {}

impl RedStrat for ArgCondEqRed {
    fn name(&self) -> &'static str {
        "arg_cond_eq_reduce"
    }

    fn new(_: &Instance) -> Self {
        ArgCondEqRed {}
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let now = time::Instant::now();
        let mut w = std::io::stdout();

        if conf.preproc.arg_eq_red_count_clause {
            eprintln!("{}", instance.clauses().len());
            bail!("");
        }

        let reductor = ArgCondEqReductor::new(instance)?;
        let (constraints, to_keep) = reductor.run()?;

        if cfg!(debug_assertions) {
            println!("to_keep {{");
            for (&pred, vars) in to_keep.iter() {
                if instance[pred].is_defined() {
                    continue;
                }
                print!("  {}:", instance[pred]);
                for var in vars {
                    print!(" {},", var.default_str())
                }
                println!();
            }
            println!("}}");
            println!("constraints #1 {{");
            for (&pred, term) in constraints.iter() {
                print!("  {}: ", instance[pred]);
                if instance[pred].is_defined() {
                    println!("defined {}", pred);
                    continue;
                }
                let mut w = std::io::stdout();
                let (term, _) = term;
                let term = term.iter().next().unwrap();
                term.write(&mut w, |w, var| var.default_write(w))?;
                println!();
            }
            println!("}}");

            println!("clauses_before {{");
            for (_cls_idx, cls) in instance.clauses().index_iter() {
                write!(w, "(assert (forall (")?;
                let mut inactive = 0;
                for var in &cls.vars {
                    if var.active {
                        write!(w, " (")?;
                        var.idx.default_write(&mut w)?;
                        write!(w, " {})", var.typ)?;
                    } else {
                        inactive += 1;
                    }
                }
                if inactive == cls.vars.len() {
                    write!(w, " (unused Bool)")?;
                }
                write!(w, " ) ")?;
                cls.expr_to_smt2(&mut w, &(true, &PrdSet::new(), &PrdSet::new(), instance.preds()))?;
                writeln!(w, "))")?;
            }
            println!("}}");

            println!("preds_before {{");
            for pred in instance.preds() {
                print!("  {}: ", pred.name);
                if pred.is_defined() {
                    println!("defined ");
                    continue;
                }
                let mut w = std::io::stdout();
                if let Some(term) = pred.strength() {
                    term.write(&mut w, |w, var| var.default_write(w))?;
                }
                println!();
            }
            println!("}}");
        }

        let res = instance.add_constraint_left(&constraints, &to_keep)?;

        if cfg!(debug_assertions) {
            println!("clauses_after {{");
            for (_cls_idx, cls) in instance.clauses().index_iter() {
                write!(w, "(assert (forall (")?;
                let mut inactive = 0;
                for var in &cls.vars {
                    if var.active {
                        write!(w, " (")?;
                        var.idx.default_write(&mut w)?;
                        write!(w, " {})", var.typ)?;
                    } else {
                        inactive += 1;
                    }
                }
                if inactive == cls.vars.len() {
                    write!(w, " (unused Bool)")?;
                }
                write!(w, " ) ")?;
                cls.expr_to_smt2(&mut w, &(true, &PrdSet::new(), &PrdSet::new(), instance.preds()))?;
                writeln!(w, "))")?;
            }
            println!("}}");
            println!("preds_after {{");
            for pred in instance.preds() {
                print!("  {}: ", pred.name);
                if pred.is_defined() {
                    println!("defined ");
                    continue;
                }
                if let Some(term) = pred.strength() {
                    term.write(&mut w, |w, var| var.default_write(w))?;
                }
                println!();
            }
            println!("}}");
        }

        let elapsed = now.elapsed();
        let file = conf.in_file().unwrap();
        let stats_path = Path::new(file).with_extension("stat");
        let mut file = File::create(&stats_path)?;
        writeln!(file, "time:{:?}", elapsed)?;

        Ok(res)
    }
}

/// Argument reduction context.
pub struct ArgCondEqReductor {
    /// Predicate arguments to keep.
    keep: PrdMap<VarSet>,
    instance: Arc<Instance>,
    imp_and_pos_clauses: ClsSet,
    solver: Solver<Parser>,
    data: Data,
    constraints: Candidates,
    tru_preds: PrdSet,
    fls_preds: PrdSet,
}

impl ArgCondEqReductor {
    /// Constructor.
    pub fn new(pre_instance: &PreInstance) -> Res<Self> {
        let instance = Arc::new((**pre_instance).clone());

        let mut keep = PrdMap::with_capacity(instance.preds().len());
        // Empty set for each predicate.
        for _ in instance.preds() {
            keep.push(VarSet::new())
        }

        let mut imp_and_pos_clauses = ClsSet::new();
        for (idx, clause) in instance.clauses().index_iter() {
            if clause.rhs().is_some() {
                imp_and_pos_clauses.insert(idx);
            }
        }

        let data = Data::new(instance.clone());

        let solver = conf.solver.spawn("arg_eq_red", Parser, &instance)?;

        let constraints = PrdMap::of_elems(None, instance.preds().len());
        let tru_preds = PrdSet::new();
        let fls_preds = PrdSet::new();

        Ok(ArgCondEqReductor {
            keep,
            instance,
            imp_and_pos_clauses,
            solver,
            data,
            constraints,
            tru_preds,
            fls_preds,
        })
    }

    /// Prints itself.
    #[allow(dead_code)]
    fn print(
        &mut self,
        constraints: &PrdHMap<crate::preproc::PredExtension>,
        to_keep: &PrdHMap<VarSet>,
        instance: &Instance,
    ) {
        println!("to_keep {{");
        for (&pred, vars) in to_keep {
            if instance[pred].is_defined() {
                continue;
            }
            print!("  {}:", instance[pred]);
            for var in vars {
                print!(" {},", var.default_str())
            }
            println!()
        }
        println!("}}");
        println!("constraints #2 {{");
        for (&pred, (terms, _)) in constraints {
            if instance[pred].is_defined() {
                continue;
            }
            print!("  {}: ", instance[pred]);
            let mut w = std::io::stdout();
            let _ = terms.iter().next().unwrap().write(&mut w, |w, var| var.default_write(w));
            println!()
        }
        println!("}}")
    }

    fn print2(
        &mut self,
    ) {
        println!("to_keep {{");
        for (pred, vars) in self.keep.index_iter() {
            if self.instance[pred].is_defined() {
                continue;
            }
            print!("  {}:", self.instance[pred]);
            for var in vars {
                print!(" {},", var.default_str())
            }
            println!()
        }
        println!("constraints #3 {{");
        for (pred, term) in self.constraints.index_iter() {
            print!("  {}: ", self.instance[pred]);
            if self.instance[pred].is_defined() {
                println!("defined ");
                continue;
            }
            let mut w = std::io::stdout();
            if let Some(term) = term {
                let _ = term.write(&mut w, |w, var| var.default_write(w));
            } else {
                print!("None ");
                if self.tru_preds.contains(&pred) {
                    print!("true");
                } else if self.fls_preds.contains(&pred) {
                    print!("false");
                }
            }
            println!()
        }
        println!("}}")
    }

    // Adding positive samples by self.instance.cexs_to_data for each candidate in self.constraints
    // Assumed that self.constraints has at least one canditate for one predicate?
    fn handle_candidates(&mut self) -> Res<bool> {
        smt::reset(&mut self.solver, &self.instance)?;
        self.fls_preds.clear();
        for (pred, cand) in self.constraints.index_iter() {
            if self.instance[pred].is_defined() {
                continue;
            } else if self.tru_preds.contains(&pred) {
                // skip
            } else if let Some(term) = cand {
//                println!("cand: {}", term);
                let pred = &self.instance[pred];
                let sig: Vec<_> = pred
                    .sig
                    .index_iter()
                    .map(|(var, typ)| (var, typ.get()))
                    .collect();
                self.solver.define_fun(
                    &pred.name,
                    &sig,
                    typ::bool().get(),
                    &SmtTerm::new(&term),
                )?;
            } else {
                self.fls_preds.insert(pred);
            }
        }

        let mut cexs = ClsHMap::with_capacity(self.instance.clauses().len());
        let mut imp_and_pos_clauses = ClsSet::new();
        std::mem::swap(&mut imp_and_pos_clauses, &mut self.imp_and_pos_clauses);
        for &clause in &imp_and_pos_clauses {
            self.get_cexs_of_clause(clause, &mut cexs)?
        }
        std::mem::swap(&mut imp_and_pos_clauses, &mut self.imp_and_pos_clauses);

        let res = self.instance.cexs_to_data(&mut self.data, cexs)?;

        for cstr in self.data.constraints.clone() {
            if let Some(pos) = cstr.rhs() {
                self.data.add_pos(0.into(), pos.pred, pos.args.clone());
            }
        }
        self.data.propagate()?;

        Ok(res)
    }

    fn get_cexs_of_clause(&mut self, cls_idx: ClsIdx, map: &mut Cexs) -> Res<()> {
        let clause = &self.instance[cls_idx];

        self.solver.push(1)?;
        clause.declare(&mut self.solver)?;
        let info = (
            false,
            &self.tru_preds,
            &self.fls_preds,
            self.instance.preds(),
        );
//        dbg!(info);
//        dbg!(clause);
//        let mut w = std::io::stdout();
//        let _ = clause.expr_to_smt2(&mut w, &info)?;
//        println!("");
//        dbg!();

        self.solver.assert_with(clause, &info)?;

        let sat = self.solver.check_sat()?;
        if sat {
            let model = self.solver.get_model()?;
            let model = Parser.fix_model(model)?;
            let cex = Cex::of_model(
                clause.vars(),
                model,
                true,
            )?;
            let bias = Bias::Non;
            let cexs = vec![(cex, bias)];
            let prev = map.insert(cls_idx, cexs);
            debug_assert_eq!(prev, None)
        }

        self.solver.pop(1)?;

        Ok(())
    }

    fn construct_guard(&self, pred: PrdIdx, var_map: &Vec<VarIdx>, coefs: &mut Vec<BigInt>) -> Term {
        let mut add_terms = Vec::new();
        add_terms.push(term::int(coefs[0].clone()));
        for (i,&v) in var_map.iter().enumerate() {
            let v_term = term::var(v, self.instance[pred].sig()[v].clone());
            add_terms.push(term::cmul(coefs[i+1].clone(), v_term));
        }
        term::le(term::int_zero(), term::add(add_terms))
    }

    fn construct_equality(&self, pred: PrdIdx, var_map: &Vec<VarIdx>, coefs: &mut Vec<BigInt>) -> Term {
        let mut add_terms = Vec::new();
        let n = coefs.len();
        if n == 0 {
            term::tru()
        } else {
//            dbg!(&coefs);
            add_terms.push(term::int(coefs[n-1].clone()));
            for (i,&v) in var_map.iter().enumerate() {
                if i != n-1 {
                    let v_term = term::var(v, self.instance[pred].sig()[v].clone());
                    add_terms.push(term::cmul(coefs[i].clone(), v_term));
                }
            }
            term::eq(term::int_zero(), term::add(add_terms))
        }
    }

    fn call_external_synthesizer(&self, pred: PrdIdx, var_map: &Vec<VarIdx>, vectors: &Vec<Vec<BigInt>>) -> Res<(Term,VarSet)> {
        // Make input file
//        dbg!(vectors);
        let input = "output.csv";
        let input_path = Path::new(input);
        let cmd = "cond_eq";
        let mut file = File::create(&input_path)?;
        writeln!(file, "{}", vectors.len())?;
        for vec in vectors {
            let csv = vec.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(",");
            writeln!(file, "{}", csv)?;
        }

        // Execute synthesizer
        let _output = Command::new(cmd).arg(input).output()?;

        // Read result
        let output_path = input_path.with_extension("result");
        let reader = BufReader::new(File::open(output_path).unwrap());
        let mut r: Vec<Term> = Vec::new();
        let mut iter = reader.lines().into_iter();
        let num_cand : usize = iter.next().unwrap()?.parse().unwrap();
        let mut removes = VarSet::new();
        for _ in 1..=num_cand {
            let var_idx : usize = iter.next().unwrap()?.parse().unwrap();
            let var = var_map[var_idx];
//            dbg!(var);
            removes.insert(var.into());
            let num_conj : usize = iter.next().unwrap()?.parse().unwrap();
            let mut guard_terms: Vec<Term> = Vec::new();
            let mut and_terms = Vec::new();
            for n in 1..=num_conj {
                fn parse_csv(iter : &mut Lines<BufReader<File>>) -> Res<Vec<BigInt>> {
                    Ok (iter.next().unwrap()?.split(',').map(|s| s.parse::<BigInt>().unwrap()).collect())
                }
                let mut equality_coefs = parse_csv(&mut iter)?;
//                dbg!(&equality_coefs);
                let guard_term =
                    if n != num_conj {
                        let mut guard_coefs = parse_csv(&mut iter)?;
                        let guard_term = self.construct_guard(pred, &var_map, &mut guard_coefs);
                        guard_terms.push(guard_term.clone());
                        guard_term
                    } else {
                        term::not(term::or(guard_terms.clone()))
                    };
                let equality_term = self.construct_equality(pred, &var_map, &mut equality_coefs);
//                dbg!(&equality_term);
                let term = term::implies(guard_term, equality_term);
                and_terms.push(term);
            }
            let term = term::and(and_terms);
            r.push(term);
        }

        let mut keeps = VarSet::new();
        for (var, _) in self.instance[pred].sig().index_iter() {
            if ! removes.contains(&var) {
                keeps.insert(var);
            }
        }
        Ok ((term::and(r), keeps))
    }

    fn generate_constraints(&mut self) -> Res<()> {
        let mut raw_constraints = PrdMap::with_capacity(self.data.pos.len());
        for (pred, samples) in self.data.pos.index_iter() {
            if self.instance[pred].is_defined() {
                raw_constraints.push(None);
                continue;
            }
            if self.tru_preds.contains(&pred) {
                raw_constraints.push(None);
                continue;
            }

            if let Some(head) = samples.iter().next() {
                let mut var_map = Vec::with_capacity(head.len());
                for (var, val) in head.index_iter() {
                    if val.typ().is_int() {
                        var_map.push(var);
                    }
                }

//                dbg!(samples);

                let iter = samples.iter();
                let mut vectors = Vec::with_capacity(samples.len());
                for sample in iter {
                    let mut vector = Vec::with_capacity(var_map.len());
                    for i in 0..var_map.len() {
                        let vval = &sample[var_map[i]];
                        vector.push(vval.to_int()?.ok_or("vval is none")?);
                    }
                    vectors.push(vector);
                }
                let (term,keeps) =
                    if samples.is_empty() {
                        (term::fls(), VarSet::new())
                    } else {
                        self.call_external_synthesizer(pred, &var_map, &vectors)?
                    };
                raw_constraints.push(Some((term,keeps)));
            } else {
                raw_constraints.push(None);
            }
        }

        let mut constraints = PrdMap::new();
        let mut keeps = PrdMap::with_capacity(self.instance.preds().len());
        for (pred, raw_constraint) in raw_constraints.index_iter() {
            let mut keep = VarSet::with_capacity(self.instance[pred].sig().len());
            if self.instance[pred].is_defined() {
                constraints.push(None);
            } else if self.tru_preds.contains(&pred) {
                constraints.push(None);
                for (var, _) in self.instance[pred].sig().index_iter() {
                    keep.insert(var);
                }
            } else if let Some((term,keep_var)) = raw_constraint {
                constraints.push(Some(term.clone()));
                keep = keep_var.clone();
            } else {
                constraints.push(None);
            }

            keeps.push(keep);
        }

        self.constraints = constraints;
        self.keep = keeps;

        Ok(())
    }

    fn print_data(
        &mut self,
    ) -> Res<()> {
        println!("{}", self.data.string_do(&(), |s| s.to_string())?);
        Ok(())
    }

    /// Runs itself on all clauses of an instance.
    pub fn run(mut self) -> Res<(PrdHMap<crate::preproc::PredExtension>, PrdHMap<VarSet>)> {
        loop {
/*
            let mut s = String::new();
            let _ = std::io::stdin().read_line(&mut s);
            println!("---------------------------------------------------------------------------------");
*/
            if !self.handle_candidates()? {
                break;
            }
            self.generate_constraints()?;
            if cfg!(debug_assertions) {
                self.print2();
                self.print_data()?;
            }
        }

        let mut constraints = PrdHMap::new();
        let mut op_constraints = PrdMap::new();
        std::mem::swap(&mut op_constraints, &mut self.constraints);
        for (pred, term) in op_constraints.into_index_iter() {
            if let Some(term) = term {
                let mut set = TermSet::with_capacity(1);
                set.insert(term);
                constraints.insert(pred, (set, vec![]));
            }
        }


        let mut to_keep = PrdHMap::new();
        for (pred, vars) in ::std::mem::replace(&mut self.keep, PrdMap::new()).into_index_iter() {
            if !self.instance[pred].is_defined() {
                let prev = to_keep.insert(pred, vars);
                debug_assert! { prev.is_none() }
            }
        }

        // let tru_preds = ::std::mem::replace(&mut self.tru_preds, PrdSet::new());

        if cfg!(debug_assertions) {
            self.print(&constraints, &to_keep, &self.instance.clone());
        }

        Ok((constraints, to_keep))
    }
}
