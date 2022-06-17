using Plots
using Plots.PlotMeasures
using DelimitedFiles
using Random, Distributions

"""
Call as a jl script on any function in this file.
e.g. julia -L plot_errors.jl -e 'plot_errors(args)'.

Author: Ariel Kellison, 12/2021
"""

fpath = @__DIR__

function plot_errors(err_files::Array{String,1}, steps::Array{Int64,1})
	"""
	Args: err_files is an array of the files to be read
	"""
	# read data as matrices from files and save max from each file

	max_errs = []

	for file in err_files
		out_xv   = readdlm(file, Float64)
		# data to vec
		vec_xv       = [x::Float64 for x in out_xv]
		len          = convert(Int64,length(vec_xv)/2)
		out_dat_x    = [x for x in out_xv[1:len]]
		out_dat_v    = [v for v in out_xv[len+1:len*2]]

		norms = []

		for i = 1:length(out_dat_x)
			x    = out_dat_x[i]
			v    = out_dat_v[i]
			append!(norms, sqrt(x^2 + v^2))
		end
		append!(max_errs, maximum(norms))
	end


	norm = ((1.235*(1/10^7))^2+(6.552*(1/10^8))^2)^0.5
	bnd_array = [0.0]
	sb = 1.000003814704543
	for n in steps
		if (n >0)
			append!(bnd_array, norm*(sb^n-1)/(sb-1))
		end
	end
	print(bnd_array)
	print(max_errs)

	scatter([n for n in steps], bnd_array, label="VCFloat norm bound",
	left_margin = 15mm, right_margin = 15mm)

	plotx = scatter!(
	[n for n in steps], max_errs, ylabel = "floating-point error",xlabel = "number of steps",
	size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
	yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12,
	label="empirical error",
	title = "Leapfrog integration normwise absolute error vs iteration number"
	)

	savefig(plotx,fpath*"/normwise_errors.png")

end
