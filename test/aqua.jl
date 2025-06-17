using Aqua
Aqua.test_all(Neutrals; stale_deps = !isdefined(Base, :get_extension))
