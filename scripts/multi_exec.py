import argparse
from cbor import cbor
import sys

## Parse arguments
def parse_arguments():
    parser = argparse.ArgumentParser(description='Merge multiple CBOR files, with shared memory segments, into a single file.')
    
    parser.add_argument('--exec', metavar='name=file.cbor', action='append',
                    help='named CBOR files.')
    parser.add_argument('--equiv', metavar='a.seg==b.seg', action='append',
                    help='memory segments that must be equal')
    parser.add_argument('--verbose', '-v', action='store_true',
                    help='verbose.')
    parser.add_argument('--out', '-o', default="out.cbor",
                    help='name of output file. Default "out.cbor".')
    args = parser.parse_args()
    return args


def split_in_two(st, separator=" ", name=""):
    """Takes a text and splits it in two by a given separator.
    Unlike 'partition' it verifies that the input has exactly two
    texts separated by one spearator and reports an otherwise."""
    x = st.split(separator)
    if len(x) == 2:
        return (x[0],x[1])
    else:
        raise ValueError('ERROR parsing %r argument. It should contain exactly one %r. \n\t%r' % (name, separator,st))


## Proces the segments
def segeq_to_set(segeq):
    """Creates a set of (name, segment) pairs, from a string list of equalities.
    For example, the following string 'a.seg1==b.seg2==c.seg3' will result in
    {(a,seg1),(b,seg2),(c,seg3)}"""
    ls = segeq.split("==")
    split_dot = lambda x: split_in_two(x,separator=".",name="segment")
    set_pairs = map(split_dot, ls)
    return set(set_pairs)

## Join sets
def join_sets(sets):
    """Takes a list of sets an joins all the ones ones that intersect. You
    can think of the input as partial equ8ivalence classses and the output
    is all the disjoint equivalence classes.
    This function is slow, but is not intended to be used in large inputs."""
    disj_out = [] # Gathers all the final equivalence classes
    for set in sets:
        (join_sets, disj_sets) = ([],[])
        for out_set in disj_out:
            #append 'out_set' to the list it belongs depending on wether it intersects 'set'
            (join_sets, disj_sets)[set.isdisjoint(out_set)].append(out_set)
            
        # Join all intersecting classes with the new set
        new_class = set.union(*join_sets)
        disj_out = disj_sets + [new_class]
    return disj_out

def process_equivalences(segeq):
    """Transforms the text based list equivalences, into a list of
    disjoint lists, each containing equivalent segments.

    Input: a.seg==b.seg==c.seg c.seg1==b.segb3 b.seg==d.seg
    Output: [[('c', 'seg'), ('a', 'seg'), ('d', 'seg'), ('b', 'seg')],
             [('c', 'seg1'), ('b', 'segb3')]]
    """
    parse_text = map(segeq_to_set, segeq)
    list_segeqs = join_sets(parse_text)
    return list(map(list,list_segeqs))


## Process files and names
def name_and_file(naf):
    """Takes a text of the form 'name=filename.cbor' and splits it into
       ['name','filename.cbor']"""
    return split_in_two(naf,separator='=',name="--exec")

def load_file(name_and_filename):
    (name,filename) = name_and_filename
    """Reads a simple CBOR file. Returns version, features and compUni"""
    allCBOR = cbor.load(open(filename, 'rb'))
    return (name, allCBOR)

def join_cbors(cbor_list):
    """Accumulates the loaded CBOR into a single list, mapping names to
    CBOR.  This function also checks that all features and versions
    are the same and unifies them.

    """
    (_, (version, feature, _)) = cbor_list[0] # We assume the list is not empty
    execs = {}
    for (name, (ver, feat, cbor)) in cbor_list:
        ## Check feature
        if not feat == feature:
            raise ValueError('found files with different features: %r != %r' % (feat, feature))
        elif not ver == version:
            raise ValueError('found files with different versions: %r != %r' % (ver, version))
        ## Add cbor to dictionary, but check if the it's already there
        if name in execs:
            raise ValueError('Two files given the same name %r' % (name))
        else:
            execs[name] = cbor
    return (feature, version, execs)

def process_execs(execs):
    name_and_files = list(map(name_and_file, execs))
    opened_files = list(map(load_file, name_and_files))
    (feature, version, execs_cbor) = join_cbors(opened_files)

    return (feature, version, execs_cbor)


## Process everything
def main():
    args = parse_arguments()
    (feature, version, execs_cbor) = process_execs(args.exec)
    
    # Add 'multi-exec' flag, but warn if it's already there
    if "multi-exec" in feature:
        print("WARNING: loaded files already have 'multi-exec' flag. Nested files are not supported.")
    else:
        feature = feature + ["multi-exec"]

        
    list_segeqs = process_equivalences(args.equiv)

    #Check all segments refer to valid files
    valid_files = execs_cbor.keys()
    for segeq in list_segeqs:
        for seg in segeq:
            if not seg[0] in valid_files:
                raise ValueError('segment %r referes to file %r that is not a valid name' % (seg, seg[0]))

    multi_execs = {"execs":execs_cbor, "mem_equiv":list_segeqs}
    multi_output = [version, feature, multi_execs]
    
    write_cbor(multi_output,args.out)

def write_cbor(thing, file):
    """Encode thing as CBOR and save it to file.
    """
    with open(file, 'wb') as f:
        cbor.dump(thing, f)

try: 
    main()
except ValueError as err:
    print("Merging CBOR files FAILED.\n\n{0}".format(err))
