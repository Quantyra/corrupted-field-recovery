import gcp_cfr as c
out=c.EVIDENCE/'cfr-raw-field-coordinates-dev61-20261029T170359Z-333eff'
c.ssh('date -u\nps -eo pid,ppid,etimes,args\n',out,c.unique('shutdown-workload-review'))
