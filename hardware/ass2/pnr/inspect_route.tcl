read_db $::env(ROUTE_ODB)
puts "ALL_NETS_ROUTED [design_is_routed -verbose]"
report_wire_length -detailed_route -summary
write_def $::env(ROUTE_DEF)
