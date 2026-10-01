"""Portable path and low-priority defaults for preparation, never proof acceptance."""
from pathlib import Path
import os

def kit_paths(value, transport=None):
    kit = Path(value).resolve()
    evidence = kit / 'agent-evidence'
    assert evidence.is_dir() and (kit / 'eleven-square-lean').is_dir()
    transports = Path(transport).resolve() if transport else kit.parent
    assert transports.is_dir()
    return kit, evidence, transports

def low_priority_single_core():
    if os.name == 'nt':
        import ctypes
        k = ctypes.WinDLL('kernel32', use_last_error=True)
        k.GetCurrentProcess.restype = ctypes.c_void_p
        k.SetPriorityClass.argtypes = (ctypes.c_void_p, ctypes.c_ulong)
        k.SetProcessAffinityMask.argtypes = (ctypes.c_void_p, ctypes.c_size_t)
        handle = k.GetCurrentProcess()
        assert k.SetPriorityClass(handle, 0x4000)
        assert k.SetProcessAffinityMask(handle, 1)
    elif hasattr(os, 'sched_getaffinity'):
        os.nice(10)
        allowed = os.sched_getaffinity(0)
        os.sched_setaffinity(0, {min(allowed)})


def metadata_path(value):
    """Resolve a recorded drive path on Windows or its mounted path on Linux."""
    import re
    text=str(value).replace(chr(92),'/')
    if os.name=='nt':
        match=re.match(r'^/mnt/([a-zA-Z])/(.*)$',text)
        if match:text=match[1].upper()+':/'+match[2]
    else:
        match=re.match(r'^([a-zA-Z]):/+(.*)$',text)
        if match:text='/mnt/'+match[1].lower()+'/'+match[2]
    return Path(text)
