using Plots
using Plots.PlotMeasures
using DelimitedFiles
using Random, Distributions

"""
Call this as jl script on any function in this file.
e.g. julia -L plot_errors.jl -e 'main(args)'.

Out: six plots, two for each compiler (gcc,
compcert) and two for julia data.

Author: Ariel Kellison, 12/2021
"""

fpath = @__DIR__

# formally proven bound for one step of LF integration (position)
pbnd      = 4719104053608481 / 37778931862957161709568

function plot_comps(in_file::String, err_file::String)
    """
    Args: (1) in_file contains the random inputs for integration
          (2) err_file contains the errors
    
    Outputs: two plot files to local dir.
          (1) "histo_errors.png", a histogram of errors 
          (2) "scatter_errors.png", errors vs input val
    
    resource: https://docs.julialang.org/en/v1/stdlib/DelimitedFiles/
    """
    # read in data, as matrices, from files

    in_rands = readdlm(in_file, Float64)
    out_xv   = readdlm(err_file, Float64)

    # turn into vectors

    vec_in   = [x::Float64 for x in in_rands]
    vec_xv   = [x::Float64 for x in out_xv]
    len      = convert(Int64,length(vec_xv)/2)
    vec_in_x = [x for x in vec_in[1:len]]
    vec_in_v = [v for v in vec_in[len+1:len*2]]
    vec_x    = [x for x in out_xv[1:len]]
    vec_v    = [v for v in out_xv[len+1:len*2]]

    max_x    = maximum(vec_x)
    
    # plot histogram 

    plot([pbnd for i in 1:len],seriestype="vline",label="formally proven bound=$pbnd",
	left_margin = 15mm, right_margin = 15mm
	 )
    plota = histogram!(
        vec_x, xlabel = "floating-point error",ylabel = "frequency",
        label="empirical error",size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        legendfontsize=12, yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12,
        ytickfontsize = 12,
        title = "Leapfrog integration: absolute position error"
    )
    savefig(plota,fpath*"/histo_errors.png")
    
    # plot scatter

    plot([pbnd for i in -1:1],seriestype="hline",label="formally proven bound=$pbnd",
        left_margin = 15mm, right_margin = 15mm
	 )
    plotb = scatter!(
        vec_in_x, vec_x, ylabel = "floating-point error",xlabel = "initial position",
        size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12,
        label="empirical error",
        xlims = (-1,1), title = "Leapfrog integration: absolute position error"    
	)
    savefig(plotb,fpath*"/scatter_errors.png")
end

function leapfrog32(x::Float32,v::Float32,n::Int32,h::Float32)::Tuple{Float32,Float32}
    for i in 1:n
        xnew         = (x + h * v) + (h * h * - x) / 2f0
        vnew         = v + (h*(- x + - xnew)/2f0)
        x            = xnew
        v            = vnew
    end
    return (x,v)
end

function leapfrog64(x::Float32,v::Float32,n::Int32,h::Float32)::Tuple{Float64,Float64}
    for i in 1:n
        xnew         = (x + h * v) + (h * h * - x) / 2
        vnew         = v + (h*(- x + - xnew)/2)
        x            = xnew
        v            = vnew
    end
    return (x,v)
end

function plot_julia(sz)
    # choose random starting values in interval
    x2 = [Float64(rand(Uniform(-1,1))) for n in 1:sz]
    v2 = [Float64(rand(Uniform(-1,1))) for n in 1:sz]
    x1 = x2
    v1 = v2
    # define time step
    h = (1f0/32f0)
    # integrate
    LF32x = [leapfrog32(x2[i],v2[i],1f0,h)[1] for i in 1:sz]
    LF64x = [leapfrog64(x1[i],v1[i],1f0,h)[1] for i in 1:sz]
    # determine error
    xs   = [abs(LF32x[i] - LF64x[i]) for i in 1:sz]

    plot([pbnd for i in 1:sz],seriestype="vline",label="formally proven bound=$pbnd" )
    plota = histogram!(
        xs, xlabel = "floating-point error",ylabel = "frequency",
        label="empirical error",size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        legendfontsize=12, yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12,
        ytickfontsize = 12, title = "Absolute position error - Julia"
    )
    savefig(plota,fpath*"/julia_errors.png")

    plot([pbnd for i in -1:1],seriestype="hline",label="formally proven bound=$pbnd" )
    plotb = scatter!(
        x1,xs, ylabel = "floating-point error",xlabel = "position val",
        size = (900, 500),bottom_margin = 10mm,left_margin = 10mm,
        yguidefontsize=12, xguidefontsize=12, xtickfontsize = 12, ytickfontsize = 12,
        label="empirical error",
        xlims = (-1,1), title = "Absolute position error - Julia"
    )
    savefig(plotb,fpath*"/julia_errors2.png")
end

function main(file1,file2,sz)
    """
    Args: (1) in_file contains the random inputs for integration
          (2) err_file contains the errors
          (3) number of inputs for Julia plots
    """

    plot_comps(file1,file2)
    plot_julia(sz)

end
