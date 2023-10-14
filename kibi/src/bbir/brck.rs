use sti::arena_pool::ArenaPool;
use sti::vec::Vec;
use sti::keyed::{Key, KVec};

use crate::string_table::StringTable;
use crate::ast::expr::RefKind;
use crate::env::Env;

use super::*;


pub fn borrow_check<'a>(func: Function<'a>, env: &Env<'a>, strings: &StringTable, alloc: &'a Arena) -> Result<(), ()> {
    let temp = ArenaPool::tls_get_temp();

    let mut this = BrCk {
        alloc,
        env,
        strings,
        temp: &*temp,
        func,
        ref_infos: KVec::with_cap(func.vars.len()),
        block_infos: KVec::with_cap(func.blocks.len()),
        next_region: RegionId::ZERO,
    };


    // count regions.
    for (_, var) in this.func.vars.iter() {
        // @todo: count regions in reduced type.
        if let Some([_r, kind, _ty]) = var.ty.try_ref_app() {
            // @todo: whnf.
            let Some(kind) = kind.try_global() else {
                return Err(());
            };

            let kind = match kind.id {
                SymbolId::Ref_Kind_mut   => RefKind::Mut,
                SymbolId::Ref_Kind_shr   => RefKind::Shared,
                SymbolId::Ref_Kind_const => RefKind::Const,
                _ =>
                    return Err(())
            };

            this.ref_infos.push(RefInfo {
                num_regions: 1,
                kind: Some(kind),
            });
        }
        else {
            this.ref_infos.push(RefInfo {
                num_regions: 0,
                kind: None,
            });
        }
    }
    dbg!(&this.ref_infos);


    // create region vars.
    for (_, block) in this.func.blocks.iter() {
        //let mut entry_regions = Vec::with_cap_in(this.temp, this.ref_infos.len());
        let mut entry_regions = Vec::new_in(this.temp);
        for var in block.vars_entry.iter() {
            let info = &this.ref_infos[var];

            let mut regions = Vec::with_cap_in(this.temp, info.num_regions as usize);
            for _ in 0..info.num_regions {
                regions.push(this.next_region);
                this.next_region = this.next_region.add(1).unwrap();
            }
            entry_regions.push(&*regions.leak());
        }
        // @todo: sti vec shrink to fit.
        //entry_regions.shrink_to_fit();

        let mut ref_regions = Vec::new_in(this.temp);
        for stmt in block.stmts {
            if let Stmt::Ref(_) = stmt {
                ref_regions.push(this.next_region);
                this.next_region = this.next_region.add(1).unwrap();
            }
        }
        // @todo: sti vec shrink to fit.
        //ref_regions.shrink_to_fit();

        this.block_infos.push(BlockInfo {
            entry_regions: entry_regions.leak(),
            ref_regions: ref_regions.leak(),
        });
    }
    dbg!(&this.block_infos);


    // compute region subsets.
    let mut stack = Vec::with_cap(32);
    //let mut subset_builder = Vec::with_cap(2*this.ref_infos.len());
    for (bb, block) in this.func.blocks.iter() {
        let info = &this.block_infos[bb];

        let mut ref_region = 0;
        for stmt in block.stmts {
            match *stmt {
                Stmt::Error |
                Stmt::Axiom |
                Stmt::Const(_) |
                Stmt::ConstUnit |
                Stmt::ConstBool(_) |
                Stmt::ConstNat(_) => stack.push(None.into()),

                Stmt::Pop => { stack.pop().unwrap(); }

                Stmt::Ref(_) => {
                    let region = info.ref_regions[ref_region];
                    ref_region += 1;
                    stack.push(region.some());
                }

                Stmt::Read(_) => stack.push(None.into()),

                Stmt::Write(path) => {
                    stack.pop().unwrap();
                    _ = path;
                }

                Stmt::Call { func: _, num_args } => {
                    // @todo: pop_n.
                    stack.truncate(stack.len() - num_args);
                }
            }
        }
    }


    Err(())
}


struct BrCk<'me, 'a> {
    alloc: &'a Arena,
    env: &'me Env<'a>,
    #[allow(dead_code)] strings: &'me StringTable<'me>,

    temp: &'me Arena,

    func: Function<'a>,

    ref_infos: KVec<LocalVarId, RefInfo>,
    block_infos: KVec<BlockId, BlockInfo<'me>>,
    next_region: RegionId,
}


#[derive(Debug)]
struct RefInfo {
    num_regions: u32,
    kind: Option<RefKind>,
}


sti::define_key!(u32, RegionId);

#[derive(Debug)]
struct BlockInfo<'a> {
    entry_regions: &'a [&'a [RegionId]],
    ref_regions: &'a [RegionId],
}


impl<'me, 'a> BrCk<'me, 'a> {
}

