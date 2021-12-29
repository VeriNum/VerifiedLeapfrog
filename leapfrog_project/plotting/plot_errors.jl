using Plots
using Plots.PlotMeasures
using DelimitedFiles
using Random, Distributions

"""
Call as a jl script on any function in this file.
e.g. julia -L plot_errors.jl -e 'main(args)'.

Author: Ariel Kellison, 12/2021
"""

fpath = @__DIR__


# formally proven bounds 
pbnd_x = 4719104053608481 / 37778931862957161709568 
pbnd_v = 4934642575282197 / 75557863725914323419136

function plot_errors(in_file::String, err_file::String, pos::Bool)
    """
    Args: (1) in_file contains the random inputs for integration
          (2) err_file contains the errors
    
    Outputs: two plot files to local dir.
          (1) "histo_errors.png", a histogram of errors 
          (2) "scatter_errors.png", errors vs input val
    
    resource: https://docs.julialang.org/en/v1/stdlib/DelimitedFiles/
    """
    # read data as matrices from files

    in_rands = readdlm(in_file, Float64)
    out_xv   = readdlm(err_file, Float64)

    # data to vec

    vec_in   = [x::Float64 for x in in_rands]
    vec_xv   = [x::Float64 for x in out_xv]
    len      = convert(Int64,length(vec_xv)/2)
    vec_in_x = [x for x in vec_in[1:len]]
    vec_in_v = [v for v in vec_in[len+1:len*2]]
    vec_x    = [x for x in out_xv[1:len]]
    vec_v    = [v for v in out_xv[len+1:len*2]]

    max_x    = maximum(vec_x)

    # plot position or velocity

    pos ? fstr      = "position" : fstr      = "velocity"
    pos ? pbnd      = pbnd_x     : pbnd      = pbnd_v
    pos ? out_dat   = vec_x      : out_dat   = vec_v
    pos ? in_dat    = vec_in_x   : in_dat    = vec_out_v

    # plot histogram 

    plot([pbnd for i in 1:len],seriestype="vline",label="formally proven bound=$pbnd",
	left_margin = 15mm, right_margin = 15mm
	 )
    plota = histogram!(
        out_dat, xlabel = "floating-point error",ylabel = "frequency",
        label="empirical error",size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        legendfontsize=12, yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12,
        ytickfontsize = 12,
        title = "Leapfrog integration: absolute $fstr error"
    )
    savefig(plota,fpath*"/histo_errors_$fstr.png")
    
    # plot scatter

    plot([pbnd for i in -1:1],seriestype="hline",label="formally proven bound=$pbnd",
        left_margin = 15mm, right_margin = 15mm
	 )
    plotb = scatter!(
        in_dat, out_dat, ylabel = "floating-point error",xlabel = "initial $plot_l",
        size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12,
        label="empirical error",
        xlims = (-1,1), title = "Leapfrog integration: absolute $fstr error"    
	)
    savefig(plotb,fpath*"/scatter_errors_$fstr.png")
end
