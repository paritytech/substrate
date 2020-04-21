#!/usr/bin/env ruby
#

def run_bench(multiplier, start_range, end_range)
	range = (start_range..end_range)
	range.each { |n|
		n = n * multiplier
		n = n.to_s.rjust(4, "0")
		puts "Running benchmark with #{n} tx per block"
		env_vars = {
			"SP_PROFILER" => "async", 
			"SP_PROFILER_FILENAME" => "noop-results_#{n}_tx_per_block.csv",
			"TX_PER_BLOCK" => "#{n}"
		}
		res = system(env_vars, "cargo run --release -p node-bench -- ::node::import::wasm::sr25519::medium")
		puts "Done, success = #{res}"
	}
end

run_bench(1, 0, 9)
run_bench(10, 1, 9)
run_bench(100, 1, 20)
