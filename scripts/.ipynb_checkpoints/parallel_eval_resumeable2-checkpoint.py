"""
  Wrapper script for running the evaluation script in parallel on the declarations in a .names file
"""
import pickle as pkl
import os
import itertools
import numpy as np
import subprocess
from tqdm import tqdm
from multiprocessing.pool import ThreadPool
import multiprocessing
import re
from pathlib import Path
import datetime
import json

def files_with_extension(dir_path, ext=None):
    if ext is None:
        dataset_files = [os.path.join(dir_path, x) for x in os.listdir(dir_path)]
    else:
        dataset_files = [os.path.join(dir_path, x) for x in os.listdir(dir_path) if re.search(r"." + ext, x)] # TODO(jesse): test
    return dataset_files

def _parse_main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("n_workers", type=int)
    parser.add_argument("decls_per_shard", type=int)
    parser.add_argument("decls_file")
    parser.add_argument("dest_dir")
    parser.add_argument("--max_tokens", type=int)
    parser.add_argument("--temperature", type=float)
    parser.add_argument("--top_p", type=float)
    parser.add_argument("--n", type=int)
    parser.add_argument("--best_of", type=int)
    parser.add_argument("--fuel", type=int)
    parser.add_argument("--engine_id")
    parser.add_argument("--api_key")
    parser.add_argument("--nbest", type=int)
    parser.add_argument("--beam", type=int)
    parser.add_argument("--model_path")
    parser.add_argument("--data_path")
    parser.add_argument("--entry_pt")
    parser.add_argument("--max_width", help="maximum size of search queue for BFS")
    parser.add_argument("--max_depth", help="maximum distance of search node from root before the search queue rejects it")

    parser.add_argument("--lean_threads", help="number of threads per Lean process", default=None)
    parser.add_argument("--lean_timeout", help="deterministic timeout for Lean process in millions of allocations. Interactive default is one. Default is unbounded (none).", default=None)

    parser.add_argument("--api", default="gptf", 
        help="gptf|baseline|fairseq|gptf_neo|gptf_neo_withoutparsing|gptf_neo_8epoch")
    parser.add_argument("--search_strategy", default="greedy", help="greedy|bfs")
    parser.add_argument("--tac_timeout", default=5, help="tactic execution timeout (s)", type=int)
    parser.add_argument("--global_timeout", default=300, help="proof search timeout (s)", type=int)
    return parser.parse_args()

def eval_decls_step(decl_file: str, dest: str, opts, eval_decls_state, lock):
#     print("Here!")
    lock.acquire()
#     print(f"Checking {decl_file}, and it's done: {eval_decls_state.is_done(decl_file)}")
    if eval_decls_state.is_done(decl_file):
        lock.release()
        return decl_file, None
    lock.release()
    
    strat = opts.search_strategy
    try:
        assert strat in ["bfs", "greedy"]
    except AssertionError:
        raise Exception("[parallel_eval] ERROR: must specify `search_strategy` = `bfs` or `greedy`")

    if not opts.api == "baseline":
        try:
            assert opts.n <= opts.best_of
        except AssertionError:
            raise Exception(f"[parallel_eval] ERROR: opts.n ({opts.n}) must be less than or equal to opts.best_of ({opts.best_of})")
    if strat == "bfs" and (opts.max_width is None or opts.max_depth is None):
        raise Exception("[parallel_eval] ERROR: max_width and max_depth must be set for BFS")
    if opts.api == "baseline":
        lean_script = f"./src/evaluation/{strat}/baseline.lean" 
    elif opts.api == "gptf": 
        lean_script = f"./src/evaluation/{strat}/gptf.lean" 
    elif opts.api =="fairseq": 
        lean_script = f"./src/evaluation/{strat}/fairseq.lean"
    elif opts.api =="gptf_neo": 
        lean_script = f"./src/evaluation/{strat}/gptf_neo.lean"
    elif opts.api =="gptf_neo_withoutparsing": 
        lean_script = f"./src/evaluation/{strat}/gptf_neo_withoutparsing.lean"
    elif opts.api =="gptf_neo_8epoch": 
        lean_script = f"./src/evaluation/{strat}/gptf_neo_8epoch.lean"
    elif opts.api =="gptf_neo_16epoch": 
        lean_script = f"./src/evaluation/{strat}/gptf_neo_16epoch.lean"
    elif opts.api =="gptf_neo_32epoch": 
        lean_script = f"./src/evaluation/{strat}/gptf_neo_32epoch.lean"
    import os
    from os.path import expanduser, join
    home = expanduser("~")
#     state_dict = torch.load(os.path.join(home, 'data/GPT2/gpt2-pytorch_model.bin')
    lean_cmd = [os.path.join(home, ".elan/bin/lean")]
    lean_cmd += [f"--threads={opts.lean_threads}"] if opts.lean_threads is not None else []
    lean_cmd += [f"--timeout={opts.lean_timeout}000000"] if opts.lean_timeout is not None else []
    lean_cmd += ["--run"]
    lean_cmd += [lean_script] # TODO(jesse): don't use relative path
    lean_cmd += [decl_file]
    lean_cmd += [dest]
    if opts.api == "baseline":
        lean_cmd += list(map(str, [opts.fuel, opts.tac_timeout, opts.global_timeout])) if strat == "greedy" else list(map(str, [opts.fuel, opts.max_width, opts.max_depth, opts.tac_timeout, opts.global_timeout]))
    elif opts.api == "gptf":
        if strat == "greedy":
          extra_args = [opts.max_tokens, opts.temperature, opts.top_p, opts.n, opts.best_of, opts.fuel, opts.engine_id, opts.api_key, opts.tac_timeout, opts.global_timeout]
        else: # bfs
          extra_args = [opts.max_tokens, opts.temperature, opts.top_p, opts.n, opts.best_of, opts.fuel, opts.max_width, opts.max_depth, opts.engine_id, opts.api_key, opts.tac_timeout, opts.global_timeout]
        assert not any(x is None for x in extra_args)
        lean_cmd += list(map(str, extra_args))
    elif opts.api == "fairseq":
        # TODO(yuhuai)
        extra_args = [opts.max_tokens, opts.temperature, opts.nbest, opts.beam, opts.fuel, opts.entry_pt, opts.model_path, opts.data_path, opts.tac_timeout, opts.global_timeout]
        assert not any(x is None for x in extra_args)
        lean_cmd += list(map(str, extra_args))
    elif opts.api == "gptf_neo":
        extra_args = [opts.max_tokens, opts.temperature, opts.top_p, opts.n, opts.best_of, opts.fuel, opts.max_width, opts.max_depth, opts.engine_id, opts.api_key, opts.tac_timeout, opts.global_timeout]
        assert not any(x is None for x in extra_args)
        lean_cmd += list(map(str, extra_args))
    elif opts.api == "gptf_neo_withoutparsing":
        extra_args = [opts.max_tokens, opts.temperature, opts.top_p, opts.n, opts.best_of, opts.fuel, opts.max_width, opts.max_depth, opts.engine_id, opts.api_key, opts.tac_timeout, opts.global_timeout]
        assert not any(x is None for x in extra_args)
        lean_cmd += list(map(str, extra_args))
    elif opts.api == "gptf_neo_8epoch":
        extra_args = [opts.max_tokens, opts.temperature, opts.top_p, opts.n, opts.best_of, opts.fuel, opts.max_width, opts.max_depth, opts.engine_id, opts.api_key, opts.tac_timeout, opts.global_timeout]
        assert not any(x is None for x in extra_args)
        lean_cmd += list(map(str, extra_args))
    elif opts.api == "gptf_neo_16epoch":
        extra_args = [opts.max_tokens, opts.temperature, opts.top_p, opts.n, opts.best_of, opts.fuel, opts.max_width, opts.max_depth, opts.engine_id, opts.api_key, opts.tac_timeout, opts.global_timeout]
        assert not any(x is None for x in extra_args)
        lean_cmd += list(map(str, extra_args))
    elif opts.api == "gptf_neo_32epoch":
        extra_args = [opts.max_tokens, opts.temperature, opts.top_p, opts.n, opts.best_of, opts.fuel, opts.max_width, opts.max_depth, opts.engine_id, opts.api_key, opts.tac_timeout, opts.global_timeout]
        assert not any(x is None for x in extra_args)
        lean_cmd += list(map(str, extra_args))

    path = Path(dest)
    stdout_dest = os.path.join(str(path.parent), str(path.stem) + ".out")
    with open(stdout_dest, "w") as f:
      subprocess.run(lean_cmd, stdout=f, stderr=f)
    return (decl_file, lean_cmd)

# tracks the set of completed tasks
class EvaluationState:
    def __init__(self, decl_files, dests):
        self.done_dict = {decl_file:False for decl_file in decl_files}
        self.dests = dests
        
    def is_done(self, decl_file):
        ret = self.done_dict[decl_file]
        return ret

    def register_finished(self, task):
        self.done_dict[task] = True

def _main(opts):
    import wandb
    wandb.init(project="Proof-close-rate-test", entity="tst008")
    
    eval_decls_state_path = os.path.join(opts.dest_dir, "eval_decls_state.pkl")

    if os.path.exists(eval_decls_state_path):
        print("Found existing files! Loading..")
        with open(eval_decls_state_path, "rb") as f:
            eval_decls_state = pkl.load(f)
    else:
        with open(opts.decls_file, "r") as f:
            decls = f.readlines()
        # Split decls into batches
        num_shards = len(decls)//opts.decls_per_shard
        batch_size = opts.decls_per_shard
        batches = [decls[i*batch_size:(i+1)*batch_size] for i in range(num_shards-1)] + [decls[batch_size*(num_shards-1):]]
        split_decls_dir = os.path.join(opts.dest_dir, "split_decls/")
        if not os.path.exists(split_decls_dir):
            os.makedirs(split_decls_dir)
        # Write batches into files
        decl_files = []
        for i, batch in enumerate(batches):
            decl_file = os.path.join(split_decls_dir, f"shard_{i}.names")
            with open(decl_file, "w") as f:
                for decl in batch:
                    f.write(decl)
            decl_files.append(decl_file)
        dests = [os.path.join(opts.dest_dir, f"shard_{i}.json") for i in range(len(batches))]
        # For resuming 
        eval_decls_state = EvaluationState(decl_files, dests)
        
    eval_decls_state_path = os.path.join(opts.dest_dir, "eval_decls_state.pkl")
    parallel_eval_log_path = os.path.join(opts.dest_dir, "parallel_eval.log")
    

    m = multiprocessing.Manager()
    lock = m.Lock()
    
    # Need decl_files and dests only
    decl_files = eval_decls_state.done_dict.keys() # <--
    dests = eval_decls_state.dests
    print("Declarations left for eval:", len(decl_files))
    pool_args = [(decl_file, dest, opts, eval_decls_state, lock) for decl_file, dest in zip(decl_files, dests)]
    
    with ThreadPool(opts.n_workers) as pool:
        pbar = tqdm(total=len(eval_decls_state.done_dict))
#         pbar.update(eval_decls_state.count)
        count = 0
        pbar.refresh()
        for (decl_file, lean_cmd) in pool.imap_unordered((lambda x: eval_decls_step(*x)), pool_args):
            pbar.update(1)
            pbar.refresh()
#             eval_decls_state.count += 1
            count += 1
            lock.acquire()
            if eval_decls_state.is_done(decl_file):
                lock.release()
                continue
            lock.release()
                
            print(f"{count} JOBS FINISHED")
            
            lock.acquire()
            eval_decls_state.register_finished(decl_file)
            lock.release()
            
            with open(parallel_eval_log_path, "a") as f:
                lean_cmd = " ".join(lean_cmd)
                f.write(f"[parallel_eval] {datetime.datetime.now()} FINISHED JOB: {decl_file}\n")
                f.write(f"[parallel_eval] {datetime.datetime.now()} LEAN COMMAND: {lean_cmd}\n")
                
            # Log success percentage
            num_shards = count
            total = 0
            num_success = 0
            for i in range(num_shards):
                shard_path = os.path.join(opts.dest_dir,f"shard_{i}.json")
                if os.path.exists(shard_path):
                    with open(shard_path, 'r') as f:
                        for line in f.readlines():
                            d = json.loads(line)
                            total += 1
                            if d["success"]:
                                num_success += 1
            #                 print(d)
            wandb.log({"close_rate": num_success/total, "num_goals": total})
            print(f"Solved {num_success}/{total}, with pass rate {num_success / total}")
            lock.acquire()
            with open(eval_decls_state_path, "wb") as f:
                pkl.dump(eval_decls_state, f)
            lock.release()
    pbar.close()
if __name__ == "__main__":
    opts = _parse_main()
    _main(opts)
