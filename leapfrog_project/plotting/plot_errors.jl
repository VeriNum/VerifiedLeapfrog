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


function plot_errors(in_file::String, err_file::String, hist::Bool, nsteps::Int, xlim::Float64, pbnd_x::Float64, pbnd_v::Float64)
    """
    Args: (1) in_file contains the random inputs for integration
          (2) err_file contains the ouput errors
    
    Outputs: two plot files to local dir.
          (1) "histo_errors.png", a histogram of errors 
          (2) "scatter_errors.png", errors vs input val
    
    resource: https://docs.julialang.org/en/v1/stdlib/DelimitedFiles/
    """
    # read data as matrices from files

    in_rands = readdlm(in_file, Float64)
    out_xv   = readdlm(err_file, Float64)

    # data to vec

    vec_in       = [x::Float64 for x in in_rands]
    vec_xv       = [x::Float64 for x in out_xv]
    len          = convert(Int64,length(vec_xv)/2)
    in_dat_x     = [x for x in vec_in[1:len]]
    in_dat_v     = [v for v in vec_in[len+1:len*2]]
    out_dat_x    = [x for x in out_xv[1:len]]
    out_dat_v    = [v for v in out_xv[len+1:len*2]]

    nsteps > 1 ? fstr2 = "multi-step (n = $nsteps)" : fstr2 = "single step"


    # plot histograms 

    if hist
    	plot([pbnd_x for i in 1:len],seriestype="vline",label="VCFloat bound=$pbnd_x",
		left_margin = 15mm, right_margin = 15mm
	 	)
    	plotx = histogram!(
        	out_dat_x, xlabel = "floating-point error",ylabel = "frequency",
        	label="empirical error",size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        	legendfontsize=12, yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12,
        	ytickfontsize = 12,
        	title = "Leapfrog integration: $fstr2 absolute position error"
    	)
    	savefig(plotx,fpath*"/histo_errors_x.png")
    

   	plot([pbnd_v for i in 1:len],seriestype="vline",label="VCFloat bound=$pbnd_v",
		left_margin = 15mm, right_margin = 15mm
		 )
    	plotv = histogram!(
        	out_dat_v, xlabel = "floating-point error",ylabel = "frequency",
        	label="empirical error",size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        	legendfontsize=12, yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12,
        	ytickfontsize = 12,
        	title = "Leapfrog integration: $fstr2 absolute momentum error"
    	)
    	savefig(plotv,fpath*"/histo_errors_v_$nsteps.png")
    end

    
    plot([pbnd_x for i in -xlim:xlim],seriestype="hline",label="VCFloat bound=$pbnd_x",
        left_margin = 15mm, right_margin = 15mm)

    
    plot([9.315409e-8 for i in -xlim:xlim],seriestype="hline",label="FPTaylor bound=9.3154e-8",
        left_margin = 15mm, right_margin = 15mm)

    plotx = scatter!(
        in_dat_x, out_dat_x, ylabel = "floating-point error",xlabel = "initial position",
        size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12,
        label="empirical error",
        xlims = (-xlim,xlim), title = "Leapfrog integration: $fstr2 absolute position error"    
	)
   
    savefig(plotx,fpath*"/scatter_errors_x.png")
    
    plot([pbnd_v for i in -xlim:xlim],seriestype="hline",label="VCFloat bound=$pbnd_v",
        left_margin = 15mm, right_margin = 15mm)
    
    plotv = scatter!(
        in_dat_v, out_dat_v, ylabel = "floating-point error",xlabel = "initial momentum",
        size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12,
        label="empirical error",
        xlims = (-xlim,xlim), title = "Leapfrog integration: $fstr2 absolute momentum error"    
	)
    savefig(plotv,fpath*"/scatter_errors_v_$nsteps.png")

end
