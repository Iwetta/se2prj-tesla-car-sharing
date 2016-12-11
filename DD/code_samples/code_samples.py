# - coding: utf-8 -
import json
from google.appengine.api import urlfetch
from google.appengine.api import searchAPI

from flask.blueprints import Blueprint
from flask import render_template, abort

from auth import login_required, permission_check

bp = Blueprint('cars.client', __name__)


@bp.route('/cars/search/by-address/<str:address>')
@login_required
@permission_check
def car_search_by_address(address=None):
	response_dict = None

	# return search page
	if not address:
		return render_template("cars/search/by-address.html", menuid='cars')

	# search by address
	else:

		# get coordinates for the address
		url = 'http://maps.google.com/maps/api/geocode/json?address=' + address

		try:
			result = urlfetch.fetch(url)
			if result.status_code == 200:
				# request goes well
				response_dict = json.loads(string_received)
			else:
				return abort('Wrong request.\nError code from APIs: ' + result.status_code, 400)
		except urlfetch.Error:
			logging.exception('Caught exception fetching url: ' + url + '\n' +
							  'Inserted address: ' + address )

		if not response_dict:
			return abort('Wrong response.', 500)

		# if request to get coordinates went well
		if 'results' in response_dict and \
			'geometry' in response_dict['results'] and \
			'location' in response_dict['results']['geometry']:

			location = response_dict['results']['geometry']['location']
			loc = (location['lat'], location['lng'])

			query = "distance(car_location, geopoint(" + loc[0] + ", " + loc[1] + ")) < 6000"
			try:
				index = searchAPI.Index(config.STORE_INDEX_NAME)
				found_cars = index.search(query)
			except search.Error:
				logging.exception('Caught exception while searching for cars')
				return abort('Something goes wrong during the search.', 500)

			return render_template("cars/search/results.html", menuid='cars', found_cars=found_cars)

		else:
			return abort('Wrong response.', 500)








# - coding: utf-8 -
from flask.blueprints import Blueprint
from flask import abort, jsonify

from auth import login_required, permission_check
from models import check_car_condition, car_status, get_car_parts_with_errors
from admin import get_car_condition_from_ccs, update_car_status_to_datastore

bp = Blueprint('tasks.client', __name__)


@bp.route('/tasks/<int:task_key>/completed')
@login_required
@permission_check
def task_completed(task_key=None):
	response_d = {'task_completion': '',
				  'car_parts_with_errors': []}

	if not task_key:
		return abort('Bad request', 400)

	car_condition = get_car_condition_from_ccs()

	'''
	example:
	car_condition = {
		'car_parts_condition' = {
			'engine' = 'OK',
			'wheel_pressure' = '2.5atm',
			'oil_level' = '80%',
			'water_level' = '85%',
			'locking_mechanisms' = 'OK'
		}

	}

	'''

	if check_car_condition(car_condition['car_parts_condition']):
		# car condition is OK
		update_car_status_to_datastore(car_status['AVAILABLE'])
		response_d['task_completion'] = 'OK'
		return jsonify(response_d)
	else:
		response_d['task_completion'] = 'KO'
		response_d['car_parts_with_errors'] = get_car_parts_with_errors(car_condition['car_parts_condition'])
		return jsonify(response_d)
