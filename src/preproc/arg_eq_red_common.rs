use std::vec;
use num::Integer;
use crate::{
    Rat,
    common::*,
    data::Data,
};

/**
 * return rank
 */
pub fn gauss_jordan_elimination(vectors: &mut Vec<Vec<Rat>>) -> usize {
    let dim = if vectors.len() > 0 { vectors[0].len() } else { 0 };
    let vec_count = vectors.len();
    let mut non_zero_ind = 0;
    for vec_ind in 0..vec_count {
        'non_zero_ind: while non_zero_ind < dim {
            for i in vec_ind..vec_count {
                if !vectors[i][non_zero_ind].is_zero() {
                    vectors.swap(vec_ind, i);
                    break 'non_zero_ind;
                }
            }
            non_zero_ind += 1;
        }
        if non_zero_ind == dim {
            return vec_ind;
        }
        let denom = vectors[vec_ind][non_zero_ind].clone();
        for j in non_zero_ind..dim {
            vectors[vec_ind][j] /= denom.clone();
        }
        for i in 0..vec_count {
            if i == vec_ind {
                continue;
            }
            let mult = vectors[i][non_zero_ind].clone();
            for j in non_zero_ind..dim {
                let x = vectors[vec_ind][j].clone() * mult.clone();
                vectors[i][j] -= x;
            }
        }
    }
    return vec_count;
}

pub fn generate_candidates(data: &mut Data, instance: &mut Arc<Instance>, tru_preds: &mut PrdSet) -> Res<(Candidates, PrdMap<VarSet>)> {
    let mut raw_constraints = PrdMap::with_capacity(data.pos.len());
    for (pred, samples) in data.pos.index_iter() {
        if instance[pred].is_defined() {
            raw_constraints.push(None);
            continue;
        }
        if tru_preds.contains(&pred) {
            raw_constraints.push(None);
            continue;
        }

        println!("|samples|: {}", samples.len());
        let mut iter = samples.iter();
        if let Some(base) = iter.next() {
            println!("  base: {}", base);
            let mut var_map = Vec::with_capacity(base.len());
            let mut base_vector = Vec::with_capacity(base.len());
            for (var, val) in base.index_iter() {
                if val.typ().is_int() {
                    var_map.push(var);
                    base_vector.push(base[var].to_int()?.ok_or("base[var] is none")?);
                }
            }

            let mut vectors = Vec::with_capacity(samples.len() - 1);
            for sample in iter {
                let mut vector = Vec::with_capacity(var_map.len());
                for i in 0..var_map.len() {
                    let vval = &sample[var_map[i]];
                    debug_assert!(vval.typ().is_int());
                    let vval = vval.to_int()?.ok_or("vval is none")?;
                    let bval = base_vector[i].clone();
                    vector.push(Rat::from(vval - bval));
                }
                vectors.push(vector);
            }
            let rank = gauss_jordan_elimination(&mut vectors);
            raw_constraints.push(Some((var_map, base_vector, vectors, rank)));
        } else {
            raw_constraints.push(None);
        }
    }

    let mut constraints = PrdMap::new();
    let mut keeps = PrdMap::with_capacity(instance.preds().len());
    for (pred, raw_constraint) in raw_constraints.index_iter() {
        let mut keep = VarSet::with_capacity(instance[pred].sig().len());
        if instance[pred].is_defined() {
            constraints.push(None);
        } else if tru_preds.contains(&pred) {
            constraints.push(None);
            for (var, _) in instance[pred].sig().index_iter() {
                keep.insert(var);
            }
        } else if let Some((var_map, base_vector, vectors, rank)) = raw_constraint {
            let rank = *rank;
            let dim = var_map.len();
            if dim <= rank {
                tru_preds.insert(pred);
                constraints.push(None);
                for (var, _) in instance[pred].sig().index_iter() {
                    keep.insert(var);
                }
            } else {
                let mut pivot_indices = Vec::with_capacity(rank);
                let mut non_pivot_indices = Vec::with_capacity(dim - rank);

                {
                    let mut non_zero_ind = 0;
                    for (var, _) in instance[pred].sig().index_iter() {
                        keep.insert(var);
                    }
                    for param_ind in 0..rank {
                        while vectors[param_ind][non_zero_ind].is_zero() {
                            keep.remove(&var_map[non_zero_ind]);
                            non_pivot_indices.push(non_zero_ind);
                            non_zero_ind += 1;
                        }
                        pivot_indices.push(non_zero_ind);
                        non_zero_ind += 1;
                    }
                    for i in non_zero_ind..dim {
                        keep.remove(&var_map[i]);
                        non_pivot_indices.push(i);
                    }
                }


                let mut and_terms = Vec::with_capacity(dim - rank);
                for var_ind in non_pivot_indices.into_iter() {
                    let mut const_part = Rat::from(base_vector[var_ind].clone());
                    let mut coef_part = Vec::with_capacity(rank);
                    for i in 0..rank {
                        const_part -= vectors[i][var_ind].clone() * Rat::from(base_vector[pivot_indices[i]].clone());
                        coef_part.push(vectors[i][var_ind].clone());
                    }
                    let mut denom_lcm = const_part.denom().clone();
                    for i in 0..coef_part.len() {
                        denom_lcm = denom_lcm.lcm(coef_part[i].denom());
                    }
                    const_part *= Rat::from(denom_lcm.clone());
                    for i in 0..coef_part.len() {
                        coef_part[i] *= Rat::from(denom_lcm.clone());
                    }

                    let const_part = const_part.to_integer();
                    let coef_part: Vec<_> = coef_part.iter().map(|x| x.to_integer()).collect();

                    let mut add_terms = Vec::with_capacity(1 + coef_part.len());
                    if !const_part.is_zero() {
                        add_terms.push(term::int(const_part));
                    }
                    for i in 0..coef_part.len() {
                        if !coef_part[i].is_zero() {
                            let var_ind = pivot_indices[i];
                            let var = var_map[var_ind];
                            let var_term = term::var(var, instance[pred].sig()[var].clone());
                            let mul_term = term::mul(vec![var_term, term::int(coef_part[i].clone())]);
                            add_terms.push(mul_term);
                        }
                    }
                    let add_term = if add_terms.is_empty() { term::int_zero() } else { term::add(add_terms) };
                    let lhs_term = {
                        let var = var_map[var_ind];
                        let var_term = term::var(var, instance[pred].sig()[var].clone());
                        term::mul(vec![var_term, term::int(denom_lcm)])
                    };
                    let and_term = term::eq(lhs_term, add_term);
                    and_terms.push(and_term);
                }

                let term = term::and(and_terms);
                constraints.push(Some(term));
            }
        } else {
            constraints.push(None);
        }

        keeps.push(keep);
    }

    Ok((constraints, keeps))
}
