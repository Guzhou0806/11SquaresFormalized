"""Pure scheduling/reporting policies; these functions never accept a proof.

The caller must first validate source reservations, readiness, worker ownership,
and its global concurrency ceiling. Stable sorting preserves the caller's order
among equally ranked full cases or dependency groups.
"""
import argparse
import datetime
import json
import statistics


def group_case(task):
    assert task.startswith('library-case')
    return int(task.split('library-case', 1)[1].split('-', 1)[0])


def prioritize_ready_candidates(candidates, active_jobs, last_case_starts=None):
    """Full cases first; fewer active groups, oldest waiting case, longest path.

    Pass comparable timestamps for each case's last group assignment. Recompute
    after every actual assignment, updating active_jobs and last_case_starts,
    so simultaneous free slots rotate fairly. This function starts no jobs.
    """
    last_case_starts = last_case_starts or {}
    counts = {}
    for job in active_jobs:
        if job['kind'] == 'library':
            number = group_case(job['task'])
            counts[number] = counts.get(number, 0) + 1

    def priority(row):
        if row['kind'] == 'case':
            return (0, 0, 0, 0)
        case = group_case(row['task'])
        return (1, counts.get(case, 0), last_case_starts.get(case, 0),
                -row.get('dependency_path', 0))

    return sorted(candidates, key=priority)


def should_defer_history_refresh(*, from_dispatcher, kind, event_status,
                                full_case_count, required_cases=173,
                                refresh_all=False):
    """Defer aggregate rescans only; preserve every actual group audit/receipt."""
    return (not refresh_all and from_dispatcher and kind == 'library'
            and event_status in {'CHECK_PASSED', 'CHECK_FAILED'}
            and full_case_count < required_cases)


def refill_observations(events, cut_utc, snapshot_utc=None, window=20):
    """Observed next-job delay after passed library jobs; not compiler timing."""
    assert window >= 1
    cut = datetime.datetime.fromisoformat(cut_utc)
    snapshot = (datetime.datetime.fromisoformat(snapshot_utc)
                if snapshot_utc else None)
    pending = {}
    samples = {'before': [], 'after': []}
    for event in events:
        timestamp = datetime.datetime.fromisoformat(event['utc'])
        if snapshot is not None and timestamp > snapshot:
            continue
        if event['status'] == 'CHECK_PASSED' and event.get('kind') == 'library':
            pending[event['worker']] = event
        elif event['status'] == 'CHECK_STARTED' and event['worker'] in pending:
            previous = pending.pop(event['worker'])
            end = datetime.datetime.fromisoformat(previous['utc'])
            delay = (timestamp - end).total_seconds()
            if 0 <= delay < 180:
                samples['after' if end >= cut else 'before'].append({
                    'worker': event['worker'], 'completed_task': previous['task'],
                    'next_task': event['task'], 'completion_utc': previous['utc'],
                    'start_utc': event['utc'],
                    'refill_delay_seconds': round(delay, 3)})
    result = {'comparison_window_cut_utc': cut_utc, 'median_window': window,
              'meaning': 'Observational dispatch and polling intervals, not a controlled compiler benchmark.'}
    for key, values in samples.items():
        recent = values[-window:]
        result[key + '_eligible_sample_count'] = len(values)
        result[key + '_median_window_count'] = len(recent)
        result[key + '_recent_samples'] = recent
        if recent:
            result[key + '_median_refill_delay_seconds'] = statistics.median(
                row['refill_delay_seconds'] for row in recent)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Read existing dispatch events; do not start jobs.')
    parser.add_argument('--events', required=True, help='JSON event list or pool status containing events')
    parser.add_argument('--cut', required=True, help='ISO 8601 comparison timestamp')
    parser.add_argument('--snapshot', help='Optional upper timestamp for reproducible observations')
    parser.add_argument('--window', type=int, default=20)
    args = parser.parse_args()
    with open(args.events, encoding='utf-8') as source:
        data = json.load(source)
    events = data['events'] if isinstance(data, dict) else data
    print(json.dumps(refill_observations(events, args.cut, args.snapshot, args.window), indent=2))
