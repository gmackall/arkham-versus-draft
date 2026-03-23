from flask import Flask, render_template, request, redirect, url_for
import requests
import json
import os
import csv
from datetime import datetime, timedelta
import threading
from collections import defaultdict

app = Flask(__name__)

# Cache configuration
PACKS_CACHE_FILE = 'arkham_packs_cache.json'
CARDS_CACHE_FILE = 'arkham_cards_cache.json'
TABOO_CACHE_FILE = 'arkham_taboo_cache.json'
PACK_CARDS_CACHE_DIR = 'pack_cards_cache'
CACHE_DURATION_HOURS = 168 # Cache for a week
PACKS_API_URL = 'https://arkhamdb.com/api/public/packs/'
CARDS_API_URL = 'https://arkhamdb.com/api/public/cards/'
TABOO_API_URL = 'https://arkhamdb.com/api/public/taboos/'
ARKHAMDB_BASE_URL = 'https://arkhamdb.com'

# Thread locks to prevent duplicate concurrent cache refreshes
_cache_refresh_locks = defaultdict(threading.Lock)

# Faction to Magic color mapping
FACTION_COLOR_MAP = {
    'guardian': ['U'], 
    'seeker': ['W'],   
    'rogue': ['G'],    
    'mystic': ['B'],   
    'survivor': ['R'], 
    'neutral': [],     
}

# Type code to Magic type mapping
TYPE_CODE_MAP = {
    'investigator': 'Creature',
    'asset': 'Artifact',
    'event': 'Instant',
    'skill': 'Sorcery', 
    'treachery': 'Enchantment',
}

def get_investigator_colors(card):
    """Get colors for an investigator based on deck_options instead of faction_code."""
    if card.get('type_code') != 'investigator':
        # For non-investigators, use the original faction_code logic
        return FACTION_COLOR_MAP.get(card.get('faction_code', 'neutral'), [])
    
    # For investigators, extract factions from deck_options
    deck_options = card.get('deck_options', [])
    unique_factions = set()
    
    for option in deck_options:
        factions = option.get('faction', [])
        for faction in factions:
            if faction != 'neutral':  # Exclude neutral as specified
                unique_factions.add(faction)
    
    # Convert factions to colors and sort for consistency
    colors = []
    for faction in sorted(unique_factions):
        faction_colors = FACTION_COLOR_MAP.get(faction, [])
        colors.extend(faction_colors)
    
    # Remove duplicates while preserving order
    unique_colors = []
    for color in colors:
        if color not in unique_colors:
            unique_colors.append(color)
    
    return unique_colors

def format_image_url(image_src):
    """Format image URL by prepending ArkhamDB base URL if needed."""
    if not image_src:
        return ''
    if image_src.startswith('http'):
        return image_src  # Already a full URL
    return ARKHAMDB_BASE_URL + image_src

def parse_excluded_cards(excluded_text):
    """Parse the excluded cards text and return a set of normalized card names."""
    if not excluded_text:
        return set()
    
    excluded_cards = set()
    lines = excluded_text.strip().split('\n')
    
    for line in lines:
        line = line.strip()
        if not line:
            continue
        
        # Parse format like "1 Knife" or "2 Emergency Cache"
        # Split on first space and take everything after the first word (which should be a number)
        parts = line.split(' ', 1)
        if len(parts) >= 2:
            try:
                # Try to parse the first part as a number to validate format
                int(parts[0])
                card_name = parts[1].strip()
                if card_name:
                    # Normalize card name for matching (case-insensitive)
                    excluded_cards.add(card_name.lower())
            except ValueError:
                # If first part isn't a number, treat the whole line as a card name
                excluded_cards.add(line.lower())
        else:
            # If there's no space, treat the whole line as a card name
            excluded_cards.add(line.lower())
    
    return excluded_cards

def parse_cards_to_include(include_text):
    """Parse the cards to include text and return a dict with card names, quantities, and types."""
    if not include_text:
        return {}
    
    cards_to_include = {}
    try:
        lines = include_text.strip().split('\n')
        
        # Get card database for type lookup
        arkham_cards = get_arkham_cards()
        card_name_to_data = {}
        if arkham_cards:
            for card in arkham_cards:
                card_name = card.get('name', '').lower()
                if card_name:
                    # Prioritize main cards over bonded cards
                    # If we already have this card name, only replace if the new one is NOT a bonded card
                    # or if we don't have a main card yet
                    existing = card_name_to_data.get(card_name)
                    if existing is None:
                        # First card with this name
                        card_name_to_data[card_name] = card
                    elif existing.get('bonded_to') and not card.get('bonded_to'):
                        # Replace bonded card with main card
                        card_name_to_data[card_name] = card
                    elif not existing.get('bonded_to') and not card.get('bonded_to'):
                        # Both are main cards, prefer the one with deck requirements (for investigators)
                        if card.get('type_code') == 'investigator' and card.get('deck_requirements', {}).get('card'):
                            card_name_to_data[card_name] = card
        
        for line in lines:
            line = line.strip()
            if not line:
                continue
            
            # Parse format like "1 Knife" or "2 Emergency Cache"
            parts = line.split(' ', 1)
            if len(parts) >= 2:
                try:
                    quantity = int(parts[0])
                    card_name = parts[1].strip()
                    if card_name:
                        # Look up card type
                        card_data = card_name_to_data.get(card_name.lower())
                        card_type = 'player'  # default
                        
                        if card_data:
                            if card_data.get('type_code') == 'investigator':
                                card_type = 'investigator'
                            elif card_data.get('subtype_code') == 'basicweakness':
                                card_type = 'basicweakness'
                            else:
                                card_type = 'player'
                        
                        cards_to_include[card_name.lower()] = {
                            'name': card_name,
                            'quantity': quantity,
                            'type': card_type,
                            'data': card_data
                        }
                except ValueError:
                    # If first part isn't a number, skip this line
                    continue
    except Exception as e:
        print(f"Error in parse_cards_to_include: {e}")
        return {}
    
    return cards_to_include

def add_cards_to_include_to_lists(cards_to_include, investigators_cards, basic_weaknesses_cards, player_cards, arkham_cards, existing_custom_cards=None):
    """Add cards to include to the appropriate card lists and update custom cards."""
    if not cards_to_include:
        return investigators_cards, basic_weaknesses_cards, player_cards, []
    
    custom_cards = []
    
    # Track cards that have already been added to prevent duplicates
    # Include existing custom cards from pack selection
    added_card_names = set()
    if existing_custom_cards:
        for card in existing_custom_cards:
            added_card_names.add(card.get('name', '').lower())
    
    for card_name_lower, card_info in cards_to_include.items():
        card_name = card_info['name']
        quantity = card_info['quantity']
        card_type = card_info['type']
        card_data = card_info['data']
        
        # Skip if this card has already been added
        if card_name.lower() in added_card_names:
            print(f"Skipping duplicate card: {card_name}")
            continue
            
        # Mark this card as added
        added_card_names.add(card_name.lower())
        
        # Create a custom card entry if we have the card data
        if card_data:
            # Use the exact same logic as convert_to_draftmancer_format
            # Convert cost to string, handle special cases
            cost = card_data.get('cost')
            if cost == -2:
                mana_cost_str = "X"
            elif cost is not None:
                mana_cost_str = str(cost)
            else:
                mana_cost_str = "0"
            
            # Create custom card entry using the exact same format as main processing
            custom_card = {
                "name": card_name,
                "image": format_image_url(card_data.get('imagesrc', '')),
                "colors": get_investigator_colors(card_data),
                "mana_cost": mana_cost_str,
                "type": TYPE_CODE_MAP.get(card_data.get('type_code'), 'Instant'),
                "set": f"AH{card_data.get('pack_code', '').upper()}",
                "collector_number": str(card_data.get('code', '001')),
                "rating": 0
            }
            
            # Add layout field for investigator cards
            if card_data.get('type_code') == 'investigator':
                custom_card["layout"] = "split_left"
            
            # Add related_cards and draft_effects (same logic as main processing)
            related_cards = []
            draft_effect_cards = []
            related_cards_to_add = []  # Cards that need custom entries too
            
            # Add deck_requirements related cards (only for investigators)
            if card_data.get('type_code') == 'investigator':
                deck_requirements = card_data.get('deck_requirements', {})
                if 'card' in deck_requirements:
                    card_req_data = deck_requirements['card']
                    if isinstance(card_req_data, dict):
                        # Get card codes from the keys of the card dictionary
                        related_card_codes = list(card_req_data.keys())
                        # Find the names of these cards
                        for code in related_card_codes:
                            related_card = next((c for c in arkham_cards if c.get('code') == code), None)
                            if related_card:
                                related_card_name = related_card.get('name', '')
                                # Only add if not already added
                                if related_card_name.lower() not in added_card_names:
                                    related_cards.append(related_card_name)
                                    # Add to draft effects so they're added to drafter's pool
                                    draft_effect_cards.append(related_card_name)
                                    # Add to list of cards that need custom entries
                                    related_cards_to_add.append(related_card)
                                    # Mark as added
                                    added_card_names.add(related_card_name.lower())
            
            # Add bonded cards to related_cards (for any card type that has them)
            bonded_cards = card_data.get('bonded_cards', [])
            if bonded_cards:
                for bonded_card_info in bonded_cards:
                    bonded_code = bonded_card_info.get('code')
                    if bonded_code:
                        bonded_card = next((c for c in arkham_cards if c.get('code') == bonded_code), None)
                        if bonded_card:
                            bonded_name = bonded_card.get('name', '')
                            # Only add if not already added
                            if bonded_name.lower() not in added_card_names:
                                related_cards.append(bonded_name)
                                # Add to draft effects so they're added to drafter's pool
                                draft_effect_cards.append(bonded_name)
                                # Add to list of cards that need custom entries
                                related_cards_to_add.append(bonded_card)
                                # Mark as added
                                added_card_names.add(bonded_name.lower())
            
            # Add related_cards if we have any
            if related_cards:
                custom_card["related_cards"] = related_cards
            
            # Add draft effects
            draft_effects = []
            
            # Add FaceUp for investigators only
            if card_data.get('type_code') == 'investigator':
                draft_effects.append("FaceUp")
                
            # Add AddCards effect if we have cards to add
            if draft_effect_cards:
                draft_effects.append({
                    "type": "AddCards",
                    "cards": draft_effect_cards
                })
                
            # Add draft_effects if we have any
            if draft_effects:
                custom_card["draft_effects"] = draft_effects
            
            # Handle back image (same logic as main processing)
            if card_data.get('backimagesrc'):
                back_card_data = {
                    "name": card_name + " - back",
                    "image": format_image_url(card_data.get('backimagesrc', '')),
                    "type": TYPE_CODE_MAP.get(card_data.get('type_code'), 'Instant')
                }
                # Add layout field for investigator back cards
                if card_data.get('type_code') == 'investigator':
                    back_card_data["layout"] = "split_left"
                custom_card["back"] = back_card_data
            
            custom_cards.append(custom_card)
            
            # Create custom card entries for all related cards too
            for related_card_data in related_cards_to_add:
                # Convert cost to string for related card
                related_cost = related_card_data.get('cost')
                if related_cost == -2:
                    related_mana_cost_str = "X"
                elif related_cost is not None:
                    related_mana_cost_str = str(related_cost)
                else:
                    related_mana_cost_str = "0"
                
                # Create custom card entry for related card
                related_custom_card = {
                    "name": related_card_data.get('name', ''),
                    "image": format_image_url(related_card_data.get('imagesrc', '')),
                    "colors": get_investigator_colors(related_card_data),
                    "mana_cost": related_mana_cost_str,
                    "type": TYPE_CODE_MAP.get(related_card_data.get('type_code'), 'Instant'),
                    "set": f"AH{related_card_data.get('pack_code', '').upper()}",
                    "collector_number": str(related_card_data.get('code', '001')),
                    "rating": 0
                }
                
                # Add layout field for investigator cards
                if related_card_data.get('type_code') == 'investigator':
                    related_custom_card["layout"] = "split_left"
                
                # Add draft effects for related cards
                related_draft_effects = []
                
                # Add FaceUp for investigators only
                if related_card_data.get('type_code') == 'investigator':
                    related_draft_effects.append("FaceUp")
                    
                # Add draft_effects if we have any
                if related_draft_effects:
                    related_custom_card["draft_effects"] = related_draft_effects
                
                # Handle back image for related cards
                if related_card_data.get('backimagesrc'):
                    related_back_card_data = {
                        "name": related_card_data.get('name', '') + " - back",
                        "image": format_image_url(related_card_data.get('backimagesrc', '')),
                        "type": TYPE_CODE_MAP.get(related_card_data.get('type_code'), 'Instant')
                    }
                    # Add layout field for investigator back cards
                    if related_card_data.get('type_code') == 'investigator':
                        related_back_card_data["layout"] = "split_left"
                    related_custom_card["back"] = related_back_card_data
                
                custom_cards.append(related_custom_card)
        
        # Add to appropriate list based on type
        if card_type == 'investigator':
            # Add to investigators list (with quantity prefix to match main generation)
            pack_code = card_data.get('pack_code', 'CUSTOM').upper() if card_data else 'CUSTOM'
            collector_number = card_data.get('code', '001') if card_data else '001'
            entry = f"{quantity} {card_name} (AH{pack_code}) {collector_number}"
            if entry not in investigators_cards:
                investigators_cards.append(entry)
        elif card_type == 'basicweakness':
            # Add to basic weaknesses list (with quantity prefix to match main generation)
            pack_code = card_data.get('pack_code', 'CUSTOM').upper() if card_data else 'CUSTOM'
            collector_number = card_data.get('code', '001') if card_data else '001'
            entry = f"{quantity} {card_name} (AH{pack_code}) {collector_number}"
            if entry not in basic_weaknesses_cards:
                basic_weaknesses_cards.append(entry)
        else:
            # Add to player cards list (with quantity prefix)
            pack_code = card_data.get('pack_code', 'CUSTOM').upper() if card_data else 'CUSTOM'
            collector_number = card_data.get('code', '001') if card_data else '001'
            entry = f"{quantity} {card_name} (AH{pack_code}) {collector_number}"
            # Check if card already exists and merge quantities
            existing_index = None
            for i, existing_entry in enumerate(player_cards):
                if card_name in existing_entry and f"(AH{pack_code})" in existing_entry:
                    existing_index = i
                    break
            
            if existing_index is not None:
                # Merge quantities
                existing_parts = player_cards[existing_index].split(' ', 1)
                try:
                    existing_quantity = int(existing_parts[0])
                    new_quantity = existing_quantity + quantity
                    player_cards[existing_index] = f"{new_quantity} {existing_parts[1]}"
                except (ValueError, IndexError):
                    # If parsing fails, just add as new entry
                    player_cards.append(entry)
            else:
                player_cards.append(entry)
    
    return investigators_cards, basic_weaknesses_cards, player_cards, custom_cards

def is_cache_valid(cache_file):
    """Check if the cache file exists and is still valid."""
    if not os.path.exists(cache_file):
        return False
    
    # Check if cache is older than CACHE_DURATION_HOURS
    cache_time = datetime.fromtimestamp(os.path.getmtime(cache_file))
    expiry_time = cache_time + timedelta(hours=CACHE_DURATION_HOURS)
    return datetime.now() < expiry_time

def cache_exists(cache_file):
    """Check if cache file exists, regardless of validity."""
    return os.path.exists(cache_file)

def refresh_cache_in_background(refresh_func, cache_key, *args):
    """Refresh cache in background thread, preventing duplicate concurrent refreshes."""
    cache_lock = _cache_refresh_locks[cache_key]
    
    def background_refresh():
        # Try to acquire the lock without blocking
        if cache_lock.acquire(blocking=False):
            try:
                print(f"Starting background refresh for {cache_key}")
                refresh_func(*args)
                print(f"Completed background refresh for {cache_key}")
            except Exception as e:
                print(f"Background cache refresh failed for {cache_key}: {e}")
            finally:
                cache_lock.release()
        else:
            print(f"Background refresh already in progress for {cache_key}, skipping")
    
    thread = threading.Thread(target=background_refresh, daemon=True)
    thread.start()

def fetch_and_cache_taboos():
    """Fetch taboo lists from API and cache them locally."""
    try:
        print(f"Fetching taboo lists from {TABOO_API_URL}")
        response = requests.get(TABOO_API_URL, timeout=10)
        response.raise_for_status()
        
        taboo_data = response.json()
        
        # Cache the data
        with open(TABOO_CACHE_FILE, 'w', encoding='utf-8') as f:
            json.dump(taboo_data, f, indent=2, ensure_ascii=False)
        
        print(f"Cached {len(taboo_data)} taboo lists")
        return taboo_data
        
    except requests.RequestException as e:
        print(f"Error fetching taboo lists from API: {e}")
        return None
    except json.JSONDecodeError as e:
        print(f"Error parsing taboo list JSON: {e}")
        return None

def load_cached_taboos():
    """Load taboo lists from cache file."""
    try:
        if os.path.exists(TABOO_CACHE_FILE):
            with open(TABOO_CACHE_FILE, 'r', encoding='utf-8') as f:
                return json.load(f)
    except Exception as e:
        print(f"Error loading cached taboo lists: {e}")
    return None

def get_arkham_taboos():
    """Get Arkham Horror taboo lists, either from cache or API."""
    # Check if we have a valid cache
    if is_cache_valid(TABOO_CACHE_FILE):
        print("Using cached taboo data")
        taboo_data = load_cached_taboos()
        if taboo_data:
            return taboo_data
    
    # Check if cache exists but is stale
    if cache_exists(TABOO_CACHE_FILE):
        print("Using stale taboo cache, refreshing in background")
        taboo_data = load_cached_taboos()
        if taboo_data:
            # Start background refresh
            refresh_cache_in_background(fetch_and_cache_taboos, "taboo_cache")
            return taboo_data
    
    # No cache exists, fetch from API synchronously
    taboo_data = fetch_and_cache_taboos()
    if taboo_data:
        return taboo_data
    
    print("Unable to load taboo data")
    return []

def fetch_and_cache_packs():
    """Fetch packs from API and cache them locally."""
    try:
        print(f"Fetching packs from {PACKS_API_URL}")
        response = requests.get(PACKS_API_URL, timeout=10)
        response.raise_for_status()
        
        packs_data = response.json()
        
        # Cache the data
        with open(PACKS_CACHE_FILE, 'w', encoding='utf-8') as f:
            json.dump(packs_data, f, indent=2, ensure_ascii=False)
        
        print(f"Successfully cached {len(packs_data)} packs")
        return packs_data
    
    except requests.RequestException as e:
        print(f"Error fetching packs from API: {e}")
        return None
    except json.JSONDecodeError as e:
        print(f"Error decoding JSON response: {e}")
        return None

def load_cached_packs():
    """Load packs from cache file."""
    try:
        with open(PACKS_CACHE_FILE, 'r', encoding='utf-8') as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"Error loading cache: {e}")
        return None

def get_packs():
    """Get Arkham Horror packs, either from cache or API."""
    # Check if we have a valid cache
    if is_cache_valid(PACKS_CACHE_FILE):
        print("Using cached packs data")
        packs_data = load_cached_packs()
        if packs_data:
            return packs_data
    
    # Check if cache exists but is stale
    if cache_exists(PACKS_CACHE_FILE):
        print("Using stale packs cache, refreshing in background")
        packs_data = load_cached_packs()
        if packs_data:
            # Start background refresh
            refresh_cache_in_background(fetch_and_cache_packs, "packs_cache")
            return packs_data
    
    # No cache exists, fetch from API synchronously
    packs_data = fetch_and_cache_packs()
    if packs_data:
        return packs_data
    
    print("Unable to load packs data")
    return []

def fetch_and_cache_cards():
    """Fetch cards from API and cache them locally."""
    try:
        print(f"Fetching cards from {CARDS_API_URL}")
        response = requests.get(CARDS_API_URL, timeout=30)  # Longer timeout for cards
        response.raise_for_status()
        
        cards_data = response.json()
        
        # Cache the data
        with open(CARDS_CACHE_FILE, 'w', encoding='utf-8') as f:
            json.dump(cards_data, f, indent=2, ensure_ascii=False)
        
        print(f"Successfully cached {len(cards_data)} cards")
        return cards_data
    
    except requests.RequestException as e:
        print(f"Error fetching cards from API: {e}")
        return None
    except json.JSONDecodeError as e:
        print(f"Error decoding JSON response: {e}")
        return None

def load_cached_cards():
    """Load cards from cache file."""
    try:
        with open(CARDS_CACHE_FILE, 'r', encoding='utf-8') as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"Error loading cards cache: {e}")
        return None

def get_pack_cards_cache_path(pack_code):
    """Get the cache file path for a specific pack."""
    if not os.path.exists(PACK_CARDS_CACHE_DIR):
        os.makedirs(PACK_CARDS_CACHE_DIR)
    return os.path.join(PACK_CARDS_CACHE_DIR, f'{pack_code}_cards.json')

def fetch_and_cache_pack_cards(pack_code):
    """Fetch cards from a specific pack and cache them."""
    try:
        pack_cards_url = f'{CARDS_API_URL}{pack_code}'
        print(f"Fetching cards from pack {pack_code}: {pack_cards_url}")
        response = requests.get(pack_cards_url, timeout=30)
        response.raise_for_status()
        
        pack_cards_data = response.json()
        
        # Cache the data
        cache_path = get_pack_cards_cache_path(pack_code)
        with open(cache_path, 'w', encoding='utf-8') as f:
            json.dump(pack_cards_data, f, indent=2, ensure_ascii=False)
        
        print(f"Successfully cached {len(pack_cards_data)} cards from pack {pack_code}")
        return pack_cards_data
    
    except requests.RequestException as e:
        print(f"Error fetching pack {pack_code} cards from API: {e}")
        return None
    except json.JSONDecodeError as e:
        print(f"Error decoding JSON response for pack {pack_code}: {e}")
        return None

def load_cached_pack_cards(pack_code):
    """Load cached cards for a specific pack."""
    cache_path = get_pack_cards_cache_path(pack_code)
    try:
        with open(cache_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"Error loading pack {pack_code} cache: {e}")
        return None

def get_pack_cards(pack_code):
    """Get cards for a specific pack, either from cache or API."""
    cache_path = get_pack_cards_cache_path(pack_code)
    
    # Check if we have a valid cache for this pack
    if is_cache_valid(cache_path):
        print(f"Using cached data for pack {pack_code}")
        pack_cards_data = load_cached_pack_cards(pack_code)
        if pack_cards_data:
            return pack_cards_data
    
    # Check if cache exists but is stale
    if cache_exists(cache_path):
        print(f"Using stale cache for pack {pack_code}, refreshing in background")
        pack_cards_data = load_cached_pack_cards(pack_code)
        if pack_cards_data:
            # Start background refresh
            refresh_cache_in_background(fetch_and_cache_pack_cards, f"pack_cards_{pack_code}", pack_code)
            return pack_cards_data
    
    # No cache exists, fetch from API synchronously
    pack_cards_data = fetch_and_cache_pack_cards(pack_code)
    if pack_cards_data:
        return pack_cards_data
    
    print(f"Unable to load cards data for pack {pack_code}")
    return []

def get_arkham_cards():
    """Get Arkham Horror cards, either from cache or API."""
    # Check if we have a valid cache
    if is_cache_valid(CARDS_CACHE_FILE):
        print("Using cached cards data")
        cards_data = load_cached_cards()
        if cards_data:
            return cards_data
    
    # Check if cache exists but is stale
    if cache_exists(CARDS_CACHE_FILE):
        print("Using stale cards cache, refreshing in background")
        cards_data = load_cached_cards()
        if cards_data:
            # Start background refresh
            refresh_cache_in_background(fetch_and_cache_cards, "cards_cache")
            return cards_data
    
    # No cache exists, fetch from API synchronously
    cards_data = fetch_and_cache_cards()
    if cards_data:
        return cards_data
    
    print("Unable to load cards data")
    return []

def load_card_evaluations():
    """Load card evaluations from CSV file and return a mapping from name to rating."""
    evaluations = {}
    csv_path = os.path.join('card_evaluation', 'card_evaluations', 'CardEvaluations.csv')
    
    try:
        with open(csv_path, 'r', encoding='utf-8') as file:
            csv_reader = csv.DictReader(file)
            for row in csv_reader:
                name = row.get('Name', '').strip()
                rating_str = row.get('Rating', '0').strip()
                try:
                    rating = int(float(rating_str))  # Convert to float first then to int to handle decimal values
                    evaluations[name] = rating
                except ValueError:
                    # If rating can't be converted to int, default to 0
                    evaluations[name] = 0
        print(f"Loaded {len(evaluations)} card evaluations")
    except FileNotFoundError:
        print(f"Warning: Could not find CardEvaluations.csv at {csv_path}")
    except Exception as e:
        print(f"Error loading card evaluations: {e}")
    
    return evaluations

def convert_to_draftmancer_format(arkham_cards, selected_pack_names, include_xp_cards=False):
    """Convert Arkham cards to Draftmancer custom card list format."""
    # Load card evaluations
    card_evaluations = load_card_evaluations()
    
    # Get pack data to map pack names to pack codes
    packs_data = get_packs()
    if not packs_data:
        packs_data = fetch_and_cache_packs()
    
    if not packs_data:
        return {"error": "Unable to load pack data"}
    
    # Create a mapping from pack name to pack code
    pack_name_to_code = {pack['name']: pack['code'] for pack in packs_data}
    
    # Get pack codes for selected packs
    selected_pack_codes = set()
    for pack_name in selected_pack_names:
        pack_code = pack_name_to_code.get(pack_name)
        if pack_code:
            selected_pack_codes.add(pack_code)
    
    # Collect all required cards from deck_requirements and bonded_cards
    # These should be included even if they're from unselected packs
    required_card_codes = set()
    
    for card in arkham_cards:
        if card.get('pack_code') in selected_pack_codes:
            # For investigators, collect deck requirements
            if card.get('type_code') == 'investigator':
                deck_requirements = card.get('deck_requirements', {})
                if 'card' in deck_requirements:
                    card_req_data = deck_requirements['card']
                    if isinstance(card_req_data, dict):
                        required_card_codes.update(card_req_data.keys())
            
            # For any card type, collect bonded cards
            bonded_cards = card.get('bonded_cards', [])
            if bonded_cards:
                for bonded_card_info in bonded_cards:
                    bonded_code = bonded_card_info.get('code')
                    if bonded_code:
                        required_card_codes.add(bonded_code)

    # Filter cards from selected packs and exclude cards with XP > 0
    # Also include required cards even if they're from unselected packs
    filtered_cards = []
    for card in arkham_cards:
        card_code = card.get('code', '')
        is_from_selected_pack = card.get('pack_code') in selected_pack_codes
        is_required_card = card_code in required_card_codes
        
        if is_from_selected_pack or is_required_card:
            # Filter out cards with XP > 0 unless include_xp_cards is enabled
            xp = card.get('xp', 0)
            if include_xp_cards or xp is None or xp <= 0:
                # Skip cards with 'b' suffix that are linked backs of other cards
                code = card.get('code', '')
                if code.endswith('b'):
                    # Check if there's any card that links to this 'b' card
                    front_card_exists = any(
                        c.get('linked_to_code') == code 
                        for c in arkham_cards if c.get('pack_code') in selected_pack_codes
                    )
                    if not front_card_exists:
                        # This 'b' card is not a linked back, include it
                        filtered_cards.append(card)
                    # If it is a linked back, skip it (it will be used as back image)
                else:
                    filtered_cards.append(card)
    
    # Create a lookup for linked back cards
    linked_back_lookup = {}
    for card in arkham_cards:
        card_code = card.get('code', '')
        is_from_selected_pack = card.get('pack_code') in selected_pack_codes
        is_required_card = card_code in required_card_codes
        
        if is_from_selected_pack or is_required_card:
            linked_to = card.get('linked_to_code')
            if linked_to and linked_to.endswith('b'):
                # Find the linked back card
                back_card = next((c for c in arkham_cards if c.get('code') == linked_to), None)
                if back_card:
                    linked_back_lookup[card.get('code')] = back_card
    
    # Check for name conflicts among bonded cards to determine if we need unique names
    bonded_name_conflicts = set()
    name_count = {}
    for card in filtered_cards:
        if card.get('bonded_to'):
            name = card.get('name', '')
            name_count[name] = name_count.get(name, 0) + 1
    
    # Mark names that have conflicts (appear more than once)
    for name, count in name_count.items():
        if count > 1:
            bonded_name_conflicts.add(name)
    
    # Convert  to Draftmancer format for CustomCards section
    draftmancer_cards = []
    for card in filtered_cards:
        # Convert cost to string, handle special cases
        cost = card.get('cost')
        if cost == -2:
            mana_cost_str = "X"
        elif cost is not None:
            mana_cost_str = str(cost)
        else:
            mana_cost_str = "0"
                
        # Generate unique name for bonded cards only if there are name conflicts
        card_name = card.get('name', '')
        if card.get('bonded_to') and card_name in bonded_name_conflicts:
            # This is a bonded card with a name conflict, make it unique by appending the code
            card_name = f"{card_name} ({card.get('code', '')})"
                
        # Get rating from card evaluations, default to 0 if not found
        card_rating = card_evaluations.get(card_name, 0)
        
        # Append XP level to name for XP > 0 cards so upgraded versions are distinguishable
        card_xp = card.get('xp', 0)
        if include_xp_cards and card_xp is not None and card_xp > 0:
            card_name = f"{card_name} ({card_xp})"
        
        draftmancer_card = {
            "name": card_name,
            "image": format_image_url(card.get('imagesrc', '')),
            "colors": get_investigator_colors(card),
            "mana_cost": mana_cost_str,
            "type": TYPE_CODE_MAP.get(card.get('type_code'), 'Instant'),
            "set": f"AH{card.get('pack_code', '').upper()}",
            "collector_number": str(card.get('code', '')),
            "rating": card_rating
        }

        # Add layout field for investigator cards
        if card.get('type_code') == 'investigator':
            draftmancer_card["layout"] = "split_left"
        
        # Add related_cards based on deck_requirements (for investigators) and bonded_cards (for any card type)
        related_cards = []
        draft_effect_cards = []  # Cards to add to drafter's pool via AddCards effect
        
        # Add deck_requirements related cards (only for investigators)
        if card.get('type_code') == 'investigator':
            deck_requirements = card.get('deck_requirements', {})
            if 'card' in deck_requirements:
                card_data = deck_requirements['card']
                if isinstance(card_data, dict):
                    # Get card codes from the keys of the card dictionary
                    related_card_codes = list(card_data.keys())
                    # Find the names of these cards
                    for code in related_card_codes:
                        related_card = next((c for c in arkham_cards if c.get('code') == code), None)
                        if related_card:
                            card_name = related_card.get('name', '')
                            related_cards.append(card_name)
                            # Add to draft effects so they're added to drafter's pool
                            draft_effect_cards.append(card_name)
        
        # Add bonded cards to related_cards (for any card type that has them)
        bonded_cards = card.get('bonded_cards', [])
        if bonded_cards:
            for bonded_card_info in bonded_cards:
                bonded_code = bonded_card_info.get('code')
                if bonded_code:
                    bonded_card = next((c for c in arkham_cards if c.get('code') == bonded_code), None)
                    if bonded_card:
                        # Always use the unique name for bonded cards (check if they have name conflicts)
                        bonded_name = bonded_card.get('name', '')
                        if bonded_card.get('bonded_to') and bonded_name in bonded_name_conflicts:
                            bonded_name = f"{bonded_name} ({bonded_code})"
                        related_cards.append(bonded_name)
                        # Add to draft effects so they're added to drafter's pool
                        draft_effect_cards.append(bonded_name)
        
        # Add related_cards to the draftmancer card if we have any
        if related_cards:
            draftmancer_card["related_cards"] = related_cards
            
        # Add draft effects for automatic card pool additions
        draft_effects = []
        
        # Add FaceUp for investigators only
        if card.get('type_code') == 'investigator':
            draft_effects.append("FaceUp")
            
        # Add AddCards effect if we have cards to add
        if draft_effect_cards:
            draft_effects.append({
                "type": "AddCards",
                "cards": draft_effect_cards
            })
            
        # Add draft_effects if we have any
        if draft_effects:
            draftmancer_card["draft_effects"] = draft_effects
        
        # Handle back image - check for linked back card first, then backimagesrc
        card_code = card.get('code', '')
        if card_code in linked_back_lookup:
            # Use the linked back card's image
            back_card = linked_back_lookup[card_code]
            back_card_data = {
                "name": card.get('name', '') + " - back",
                "image": format_image_url(back_card.get('imagesrc', '')),
                "type": TYPE_CODE_MAP.get(card.get('type_code'), 'Instant')
            }
            # Add layout field for investigator back cards
            if card.get('type_code') == 'investigator':
                back_card_data["layout"] = "split_left"
            draftmancer_card["back"] = back_card_data
        elif card.get('backimagesrc'):
            # Use the standard backimagesrc
            back_card_data = {
                "name": card.get('name', '') + " - back",
                "image": format_image_url(card.get('backimagesrc', '')),
                "type": TYPE_CODE_MAP.get(card.get('type_code'), 'Instant')
            }
            # Add layout field for investigator back cards
            if card.get('type_code') == 'investigator':
                back_card_data["layout"] = "split_left"
            draftmancer_card["back"] = back_card_data
        
        draftmancer_cards.append(draftmancer_card)
    
    return {
        "cards": draftmancer_cards,
        "count": len(draftmancer_cards),
        "selected_packs": selected_pack_names,
        "selected_pack_codes": selected_pack_codes,
        "filtered_cards": filtered_cards  # Include filtered cards for MainSlot generation
    }

def generate_player_cards(selected_pack_codes, pack_quantities=None, excluded_cards=None, taboo_modifications=None, unique_cards_only=False, include_xp_cards=False):
    """Generate the PlayerCards section with actual card quantities from pack data, separated by set."""
    # Dictionary to track card quantities by (card_name, pack_code, collector_number) tuples
    card_set_quantities = {}
    
    # Get the main cards cache to verify which cards are player cards
    main_cards = get_arkham_cards()
    player_card_codes = set(card.get('code') for card in main_cards if card.get('code'))
    
    # Create pack code to name mapping for quantity lookup
    packs_data = get_packs()
    pack_code_to_name = {pack['code']: pack['name'] for pack in packs_data} if packs_data else {}
    
    # Initialize excluded and forbidden cards sets
    if excluded_cards is None:
        excluded_cards = set()
    
    # Extract forbidden cards from taboo modifications
    if taboo_modifications:
        forbidden_cards = set(code for code, mods in taboo_modifications.items() 
                             if any('Forbidden' in mod.get('text', '') for mod in mods))
    else:
        forbidden_cards = set()
    
    # Fetch pack-specific card data for each selected pack
    for pack_code in selected_pack_codes:
        pack_cards = get_pack_cards(pack_code)
        
        # Get the multiplier for this pack (default to 1 if not specified)
        pack_name = pack_code_to_name.get(pack_code, pack_code)
        pack_multiplier = pack_quantities.get(pack_name, 1) if pack_quantities else 1
        
        for card in pack_cards:
            # Only include cards that exist in the main cards cache (player cards)
            card_code = card.get('code', '')
            if card_code not in player_card_codes:
                continue
            
            # Skip forbidden cards from taboo list
            if card_code in forbidden_cards:
                continue
                
            # Skip cards that are bonded to other cards
            if card.get('bonded_to'):
                continue
            # Skip investigators and cards with restrictions field
            if card.get('type_code') == 'investigator':
                continue
            if 'restrictions' in card and card['restrictions']:
                continue
            # Skip basic weakness cards
            if card.get('subtype_code') == 'basicweakness':
                continue
            # Skip cards with XP > 0 (considering taboo modifications) unless include_xp_cards is enabled
            xp = apply_taboo_xp_modification(card, taboo_modifications)
            if not include_xp_cards and xp is not None and xp > 0:
                continue
            
            card_name = card.get('name', '')
            
            # Skip excluded cards (using base name before XP suffix)
            if excluded_cards and card_name.lower() in excluded_cards:
                continue
            
            # Append XP level to name for XP > 0 cards so upgraded versions are distinguishable
            if include_xp_cards and xp is not None and xp > 0:
                card_name = f"{card_name} ({xp})"
            
            collector_number = str(card.get('code', ''))
            base_quantity = card.get('quantity', 0)
            final_quantity = base_quantity * pack_multiplier
            
            if card_name and final_quantity > 0:
                # Create a key combining card name, pack code, and collector number
                card_set_key = (card_name, pack_code, collector_number)
                
                if card_set_key in card_set_quantities:
                    card_set_quantities[card_set_key] += final_quantity
                else:
                    card_set_quantities[card_set_key] = final_quantity
    
    # Generate player cards lines with actual quantities, separated by set
    card_entries = []
    
    if unique_cards_only:
        # For unique cards only, track card names to ensure no duplicates
        unique_card_names = set()
        for (card_name, pack_code, collector_number), total_quantity in card_set_quantities.items():
            if card_name not in unique_card_names:
                unique_card_names.add(card_name)
                card_entries.append(f"1 {card_name} (AH{pack_code.upper()}) {collector_number}")
    else:
        # Normal behavior: include all quantities
        for (card_name, pack_code, collector_number), total_quantity in card_set_quantities.items():
            card_entries.append(f"{total_quantity} {card_name} (AH{pack_code.upper()}) {collector_number}")
    
    # Sort the entries by card name (ignoring quantity and set)
    card_entries.sort(key=lambda x: x.split(' ', 1)[1].split(' (AH')[0])
    
    return card_entries

def get_taboo_modifications(taboo_id):
    """Get a dictionary of card code to taboo modifications from the specified taboo list."""
    if not taboo_id:
        return {}
    
    try:
        taboo_id = int(taboo_id)
    except ValueError:
        return {}
    
    taboo_lists = get_arkham_taboos()
    
    # Find the taboo list with matching ID
    selected_taboo = None
    for taboo in taboo_lists:
        if taboo.get('id') == taboo_id:
            selected_taboo = taboo
            break
    
    if not selected_taboo:
        return {}
    
    taboo_modifications = {}
    
    try:
        # Parse the cards JSON string
        import json
        cards_data = json.loads(selected_taboo.get('cards', '[]'))
        
        for card_modification in cards_data:
            code = card_modification.get('code')
            if code:
                if code not in taboo_modifications:
                    taboo_modifications[code] = []
                taboo_modifications[code].append(card_modification)
    except (json.JSONDecodeError, KeyError) as e:
        print(f"Error parsing taboo list cards: {e}")
        return {}
    
    return taboo_modifications

def get_forbidden_cards_from_taboo(taboo_id):
    """Get a set of card codes that are forbidden in the specified taboo list."""
    if not taboo_id:
        return set()
    
    taboo_modifications = get_taboo_modifications(taboo_id)
    forbidden_codes = set()
    
    for code, modification in taboo_modifications.items():
        text = modification.get('text', '')
        if 'Forbidden' in text:
            forbidden_codes.add(code)
    
    return forbidden_codes

def apply_taboo_xp_modification(card, taboo_modifications):
    """Apply XP modifications from taboo list to a card, returning the modified XP cost."""
    if not taboo_modifications:
        return card.get('xp', 0)
        
    card_code = card.get('code')
    if not card_code or card_code not in taboo_modifications:
        return card.get('xp', 0)
    
    modifications = taboo_modifications[card_code]
    base_xp = card.get('xp', 0)
    
    # Apply all XP modifications for this card (sum them up)
    total_xp_change = 0
    for mod in modifications:
        if 'xp' in mod:
            total_xp_change += mod['xp']
    
    return base_xp + total_xp_change

def generate_investigators_cards(selected_pack_codes, pack_quantities=None, excluded_cards=None, taboo_modifications=None, unique_cards_only=False):
    """Generate the Investigators section with unique cards by name+set, except Core/Revised Core are treated as same set."""
    # Dictionary to track cards by (name, normalized_pack): card_name -> {normalized_pack -> (card_data, pack_data)}
    cards_by_name_and_pack = {}
    
    # Get the main cards cache to verify which cards are player cards
    main_cards = get_arkham_cards()
    player_card_codes = set(card.get('code') for card in main_cards if card.get('code'))
    
    # Initialize excluded cards and taboo modifications
    if excluded_cards is None:
        excluded_cards = set()
    if taboo_modifications is None:
        taboo_modifications = {}
    
    # Get forbidden cards from taboo modifications
    forbidden_cards = set()
    if taboo_modifications:
        for code, mods in taboo_modifications.items():
            for mod in mods:
                if 'Forbidden' in mod.get('text', ''):
                    forbidden_cards.add(code)
                    break
    
    # Get pack data for priority logic
    packs_data = get_packs()
    pack_code_to_pack = {pack['code']: pack for pack in packs_data} if packs_data else {}
    pack_code_to_name = {pack['code']: pack['name'] for pack in packs_data} if packs_data else {}
    
    def normalize_pack_code(pack_code):
        """Normalize pack codes so that 'core' and 'rcore' are treated as the same."""
        if pack_code in ['core', 'rcore']:
            return 'core'  # Treat both as 'core'
        return pack_code
    
    # Fetch pack-specific card data for each selected pack
    for pack_code in selected_pack_codes:
        pack_cards = get_pack_cards(pack_code)
        pack_data = pack_code_to_pack.get(pack_code, {})
        
        for card in pack_cards:
            # Only include cards that exist in the main cards cache (player cards)
            card_code = card.get('code', '')
            if card_code not in player_card_codes:
                continue
            
            # Skip forbidden cards from taboo list
            if card_code in forbidden_cards:
                continue
                
            # Skip cards that are bonded to other cards
            if card.get('bonded_to'):
                continue
            # Only include investigators
            if card.get('type_code') != 'investigator':
                continue
            
            card_name = card.get('name', '')
            if not card_name:
                continue
            
            # Skip excluded cards
            if excluded_cards and card_name.lower() in excluded_cards:
                continue
            
            # Normalize the pack code (core/rcore treated as same)
            normalized_pack = normalize_pack_code(pack_code)
            
            # Initialize nested dictionary if needed
            if card_name not in cards_by_name_and_pack:
                cards_by_name_and_pack[card_name] = {}
            
            # Check if this is a better version for this name+pack combination
            if normalized_pack not in cards_by_name_and_pack[card_name]:
                cards_by_name_and_pack[card_name][normalized_pack] = (card, pack_data)
            else:
                current_card, current_pack = cards_by_name_and_pack[card_name][normalized_pack]
                
                # Priority logic for same name+pack:
                # 1. Revised core set (pack_code == 'rcore') wins over core
                # 2. Otherwise, highest cycle_position wins
                # 3. If cycle_position is tied, highest position wins
                
                if pack_code == 'rcore' and current_pack.get('code') == 'core':
                    # New card is from revised core, current is from core - upgrade
                    cards_by_name_and_pack[card_name][normalized_pack] = (card, pack_data)
                elif current_pack.get('code') == 'rcore' and pack_code == 'core':
                    # Current card is from revised core, new is from core - keep current
                    pass
                else:
                    # Compare by cycle_position and position
                    current_cycle = current_pack.get('cycle_position', 0)
                    current_pos = current_pack.get('position', 0)
                    new_cycle = pack_data.get('cycle_position', 0)
                    new_pos = pack_data.get('position', 0)
                    
                    if (new_cycle > current_cycle) or (new_cycle == current_cycle and new_pos > current_pos):
                        cards_by_name_and_pack[card_name][normalized_pack] = (card, pack_data)
    
    # Generate investigators lines (no quantities, unique by name+pack)
    card_entries = []
    
    if unique_cards_only:
        # For unique cards only, track card names to ensure no duplicates across all packs
        unique_card_names = set()
        for card_name, pack_dict in cards_by_name_and_pack.items():
            if card_name not in unique_card_names:
                unique_card_names.add(card_name)
                # Pick the first/best pack version for this card name
                for normalized_pack, (card, pack_data) in pack_dict.items():
                    collector_number = str(card.get('code', ''))
                    pack_code = card.get('pack_code', '')
                    card_entries.append(f"1 {card_name} (AH{pack_code.upper()}) {collector_number}")
                    break  # Only take the first pack version for this card name
    else:
        # Normal behavior: include all pack versions
        for card_name, pack_dict in cards_by_name_and_pack.items():
            for normalized_pack, (card, pack_data) in pack_dict.items():
                collector_number = str(card.get('code', ''))
                pack_code = card.get('pack_code', '')
                card_entries.append(f"1 {card_name} (AH{pack_code.upper()}) {collector_number}")
    
    # Sort the entries by card name, then by pack code
    card_entries.sort(key=lambda x: (x.split(' ', 1)[1].split(' (AH')[0], x.split('(AH')[1].split(')')[0]))
    
    return card_entries

def generate_basic_weaknesses_cards(selected_pack_codes, pack_quantities=None, excluded_cards=None, taboo_modifications=None, unique_cards_only=False):
    """Generate the BasicWeaknesses section with unique cards by name, prioritizing revised core then most recent."""
    # Dictionary to track best card by name: card_name -> (card_data, pack_data)
    best_cards_by_name = {}
    
    # Get the main cards cache to verify which cards are player cards
    main_cards = get_arkham_cards()
    player_card_codes = set(card.get('code') for card in main_cards if card.get('code'))
    
    # Get pack data for priority logic
    packs_data = get_packs()
    pack_code_to_pack = {pack['code']: pack for pack in packs_data} if packs_data else {}
    pack_code_to_name = {pack['code']: pack['name'] for pack in packs_data} if packs_data else {}
    
    # Initialize excluded and forbidden cards sets
    if excluded_cards is None:
        excluded_cards = set()
    
    # Extract forbidden cards from taboo modifications
    if taboo_modifications:
        forbidden_cards = set(code for code, mods in taboo_modifications.items() 
                             if any('Forbidden' in mod.get('text', '') for mod in mods))
    else:
        forbidden_cards = set()
    
    # Fetch pack-specific card data for each selected pack
    for pack_code in selected_pack_codes:
        pack_cards = get_pack_cards(pack_code)
        pack_data = pack_code_to_pack.get(pack_code, {})
        
        for card in pack_cards:
            # Only include cards that exist in the main cards cache (player cards)
            card_code = card.get('code', '')
            if card_code not in player_card_codes:
                continue
            
            # Skip forbidden cards from taboo list
            if card_code in forbidden_cards:
                continue
                
            # Skip cards that are bonded to other cards
            if card.get('bonded_to'):
                continue
            # Only include basic weakness cards
            if card.get('subtype_code') != 'basicweakness':
                continue
            
            card_name = card.get('name', '')
            if not card_name:
                continue
            
            # Skip excluded cards
            if excluded_cards and card_name.lower() in excluded_cards:
                continue
            
            # Check if this is a better version than what we have
            if card_name not in best_cards_by_name:
                best_cards_by_name[card_name] = (card, pack_data)
            else:
                current_card, current_pack = best_cards_by_name[card_name]
                
                # Priority logic:
                # 1. Revised core set (pack_code == 'rcore') wins
                # 2. Otherwise, highest cycle_position wins
                # 3. If cycle_position is tied, highest position wins
                
                if pack_code == 'rcore' and current_pack.get('code') != 'rcore':
                    # New card is from revised core, current is not
                    best_cards_by_name[card_name] = (card, pack_data)
                elif current_pack.get('code') == 'rcore' and pack_code != 'rcore':
                    # Current card is from revised core, new is not - keep current
                    pass
                else:
                    # Neither or both are revised core, compare by cycle_position and position
                    current_cycle = current_pack.get('cycle_position', 0)
                    current_pos = current_pack.get('position', 0)
                    new_cycle = pack_data.get('cycle_position', 0)
                    new_pos = pack_data.get('position', 0)
                    
                    if (new_cycle > current_cycle) or (new_cycle == current_cycle and new_pos > current_pos):
                        best_cards_by_name[card_name] = (card, pack_data)
    
    # Generate basic weaknesses lines (no quantities, just unique cards)
    # Note: Basic weaknesses are already unique by name, so unique_cards_only doesn't change behavior
    card_entries = []
    for card_name, (card, pack_data) in best_cards_by_name.items():
        collector_number = str(card.get('code', ''))
        pack_code = card.get('pack_code', '')
        card_entries.append(f"1 {card_name} (AH{pack_code.upper()}) {collector_number}")
    
    # Sort the entries by card name
    card_entries.sort(key=lambda x: x.split(' ', 1)[1].split(' (AH')[0])
    
    return card_entries

def generate_draftmancer_file_content(cards, investigators_cards, basic_weaknesses_cards, player_cards, selected_pack_names, 
                                     investigators_per_pack=3, basic_weaknesses_per_pack=3, player_cards_per_pack=15, player_card_packs_per_player=3):
    """Generate the complete Draftmancer file content in .txt format."""
    lines = []
    
    # CustomCards section
    lines.append("[CustomCards]")
    import json
    lines.append(json.dumps(cards, indent=2, ensure_ascii=False))
    
    # Settings section  
    lines.append("[Settings]")
    
    # Generate predeterminedLayouts based on player_card_packs_per_player
    predetermined_layouts = ["Investigators", "BasicWeaknesses"]
    for _ in range(player_card_packs_per_player):
        predetermined_layouts.append("PlayerCards")
    
    settings = {
        "name": "AH LCG - Versus Draft",
        "cardBack": "https://images.steamusercontent.com/ugc/786371626459887968/96D099C4BBCD944EF3935E613FDF5706E46CA25A/?imw=5000&imh=5000&ima=fit&impolicy=Letterbox&imcolor=%23000000&letterbox=false",
        "layouts": {
            "Investigators": {
                "weight": 1,
                "slots": {
                    "Investigators": investigators_per_pack
                }
            },
            "BasicWeaknesses": {
                "weight": 1,
                "slots": {
                    "BasicWeaknesses": basic_weaknesses_per_pack
                }
            },
            "PlayerCards": {
                "weight": 1,
                "slots": {
                    "PlayerCards": player_cards_per_pack
                }
            }
        },
        "predeterminedLayouts": predetermined_layouts,
        "withReplacement": False,
        "colorcolorBalance": True,
    }
    lines.append(json.dumps(settings, indent=4))
    
    # Investigators section
    lines.append("[Investigators]")
    lines.extend(investigators_cards)
    
    # BasicWeaknesses section
    lines.append("[BasicWeaknesses]")
    lines.extend(basic_weaknesses_cards)
    
    # PlayerCards section
    lines.append("[PlayerCards]")
    lines.extend(player_cards)
    
    return "\n".join(lines)

def get_packs_with_player_cards():
    """Get set of pack codes that contain player cards."""
    # Check if we have valid cards cache
    if is_cache_valid(CARDS_CACHE_FILE):
        print("Using cached cards data to determine player card packs")
        cards_data = load_cached_cards()
        if cards_data:
            pack_player_card_counts = {}
            
            for card in cards_data:
                pack_code = card.get('pack_code')
                card_type = card.get('type_code')
                
                # Player cards are: investigator, asset, event, skill, and basic weakness treacheries
                player_card_types = {'investigator', 'asset', 'event', 'skill'}
                
                # Also include player treacheries (basic weaknesses)
                if card_type == 'treachery' and card.get('subtype_code') == 'basicweakness':
                    player_card_types.add('treachery')
                
                if card_type in player_card_types:
                    if pack_code not in pack_player_card_counts:
                        pack_player_card_counts[pack_code] = 0
                    pack_player_card_counts[pack_code] += 1
            
            # Return set of pack codes that have player cards
            return set(pack_code for pack_code, count in pack_player_card_counts.items() if count > 0)
    
    # If no cards cache, fetch from API
    cards_data = fetch_and_cache_cards()
    if cards_data:
        pack_player_card_counts = {}
        
        for card in cards_data:
            pack_code = card.get('pack_code')
            card_type = card.get('type_code')
            
            # Player cards are: investigator, asset, event, skill, and basic weakness treacheries
            player_card_types = {'investigator', 'asset', 'event', 'skill'}
            
            # Also include player treacheries (basic weaknesses)
            if card_type == 'treachery' and card.get('subtype_code') == 'basicweakness':
                player_card_types.add('treachery')
            
            if card_type in player_card_types:
                if pack_code not in pack_player_card_counts:
                    pack_player_card_counts[pack_code] = 0
                pack_player_card_counts[pack_code] += 1
        
        # Return set of pack codes that have player cards
        return set(pack_code for pack_code, count in pack_player_card_counts.items() if count > 0)
    
    # If all fails, return empty set (will show no packs)
    print("Unable to determine packs with player cards")
    return set()

def get_arkham_sets_grouped():
    """Get Arkham Horror sets grouped by cycle, filtered to only include packs with player cards."""
    # Get set of pack codes that contain player cards
    player_card_pack_codes = get_packs_with_player_cards()
    
    # Get packs data using the standard caching mechanism
    packs_data = get_packs()
    if packs_data:
        # Filter to only include packs with player cards
        filtered_packs = [pack for pack in packs_data if pack.get('code') in player_card_pack_codes]
        print(f"Filtered {len(packs_data)} total packs to {len(filtered_packs)} packs with player cards")
        # Sort packs by cycle_position first, then by position
        sorted_packs = sorted(filtered_packs, key=lambda pack: (pack.get('cycle_position', 99), pack.get('position', 99)))
        return group_packs_by_cycle(sorted_packs)
    
    # All methods failed
    print("All methods failed, unable to load pack data")
    return None

def group_packs_by_cycle(packs_data):
    """Group packs by cycle_position and return structured data."""
    cycles = {}
    
    for pack in packs_data:
        cycle_pos = pack.get('cycle_position', 99)
        if cycle_pos not in cycles:
            # Special case for cycle_position 50 (Return to...)
            if cycle_pos == 50:
                cycle_name = "Return to..."
            # Special case for cycle_position 60 (Starter Decks)
            elif cycle_pos == 60:
                cycle_name = "Starter Decks"
            # Special case for cycle_position 70 (Side Stories)
            elif cycle_pos == 70:
                cycle_name = "Side Stories"
            # Special case for cycle_position 80 (Promotional)
            elif cycle_pos == 80:
                cycle_name = "Promotional"
            # Special case for cycle_position 90 (Parallel)
            elif cycle_pos == 90:
                cycle_name = "Parallel"
            else:
                cycle_name = pack['name']  # First pack in cycle becomes the cycle name
                # Remove "Investigator Expansion" suffix from cycle names
                if cycle_name.endswith(' Investigator Expansion'):
                    cycle_name = cycle_name[:-len(' Investigator Expansion')]
            
            cycles[cycle_pos] = {
                'cycle_name': cycle_name,
                'packs': []
            }
        cycles[cycle_pos]['packs'].append(pack['name'])
    
    # Convert to sorted list
    return [{'cycle_position': pos, **data} for pos, data in sorted(cycles.items())]

def get_arkham_sets():
    """Get Arkham Horror sets, either from cache or API."""
    # Get packs data using the standard caching mechanism
    packs_data = get_packs()
    if packs_data:
        # Sort packs by cycle_position first, then by position
        sorted_packs = sorted(packs_data, key=lambda pack: (pack.get('cycle_position', 99), pack.get('position', 99)))
        return [pack['name'] for pack in sorted_packs]
    
    # All methods failed
    print("All methods failed, unable to load pack data")
    return []

@app.route('/')
def index():
    arkham_sets_grouped = get_arkham_sets_grouped()
    if arkham_sets_grouped is None:
        return render_template('index.html', cycles=[], taboos=[], error="Unable to load pack data from ArkhamDB. Please try again later or check your internet connection.")
    
    # Load taboo lists
    taboo_lists = get_arkham_taboos()
    
    return render_template('index.html', cycles=arkham_sets_grouped, taboos=taboo_lists)

@app.route('/deck-exporter')
def deck_exporter():
    return render_template('deck_exporter.html')

@app.route('/sitemap.xml')
def sitemap():
    return app.send_static_file('sitemap.xml')

@app.route('/api/cards')
def api_cards():
    """Return card name to code mapping for CSV generation."""
    arkham_cards = get_arkham_cards()
    if not arkham_cards:
        return {"error": "Unable to load card data"}, 500
    
    # Create a name to code mapping, prioritizing 0 XP versions for base names
    # and providing exact mappings for cards with XP costs
    name_to_code = {}
    name_to_cards = {}
    
    # Group cards by name
    for card in arkham_cards:
        if card.get('name') and card.get('code'):
            name = card['name']
            if name not in name_to_cards:
                name_to_cards[name] = []
            name_to_cards[name].append(card)
    
    # For each card name, create mappings
    for name, cards in name_to_cards.items():
        # Sort by XP cost (0 XP first, then ascending)
        cards_sorted = sorted(cards, key=lambda c: c.get('xp', 0))
        
        # Use the first card (lowest XP) for the base name
        name_to_code[name] = cards_sorted[0]['code']
        
        # Also create explicit mappings for cards with XP costs > 0
        for card in cards:
            xp = card.get('xp', 0)
            if xp > 0:
                xp_name = f"{name} ({xp})"
                name_to_code[xp_name] = card['code']
    
    return {"cards": name_to_code}

@app.route('/draft', methods=['POST'])
def draft():
    selected_sets = request.form.getlist('sets')
    
    # Get selected taboo list
    taboo_list_id = request.form.get('tabooList', '').strip()
    taboo_modifications = get_taboo_modifications(taboo_list_id)
    
    if taboo_modifications:
        forbidden_count = len([code for code, mods in taboo_modifications.items() 
                              if any('Forbidden' in mod.get('text', '') for mod in mods)])
        print(f"Applying taboo list {taboo_list_id}: excluding {forbidden_count} forbidden cards")
    
    # Check for cards to include first
    cards_to_include_text = request.form.get('cardsToInclude', '').strip()
    
    if not selected_sets and not cards_to_include_text:
        return render_template('draft_result.html', selected_sets=[], error="No sets selected and no cards to include specified")

    # Process pack quantities - get quantities for each selected pack
    pack_quantities = {}
    for pack_name in selected_sets:
        quantity_key = f'quantity_{pack_name}'
        quantity = int(request.form.get(quantity_key, 1))  # Default to 1 if not specified
        pack_quantities[pack_name] = quantity
    
    # Parse excluded cards
    excluded_cards_text = request.form.get('cardsToExclude', '').strip()
    excluded_cards = parse_excluded_cards(excluded_cards_text)
    
    # Parse cards to include (moved earlier for validation)
    try:
        cards_to_include = parse_cards_to_include(cards_to_include_text)
        if cards_to_include:
            print(f"Including {len(cards_to_include)} custom cards: {list(cards_to_include.keys())}")
    except Exception as e:
        print(f"Error parsing cards to include: {e}")
        cards_to_include = {}
    
    # Parse layout options
    investigators_per_pack = int(request.form.get('investigatorsPerPack', 3))
    basic_weaknesses_per_pack = int(request.form.get('basicWeaknessesPerPack', 3))
    player_cards_per_pack = int(request.form.get('playerCardsPerPack', 15))
    player_card_packs_per_player = int(request.form.get('playerCardPacksPerPlayer', 3))
    unique_cards_only = request.form.get('uniqueCardsOnly') == 'on'
    include_xp_cards = request.form.get('includeXpCards') == 'on'
    
    # TODO: Implement unique cards logic when backend is ready
    if unique_cards_only:
        print("Unique cards only setting enabled - limiting each card to appear at most once")
    if include_xp_cards:
        print("Include XP cards setting enabled - including all higher level cards in the draft pool")
    
    # Get all cards and convert to Draftmancer format
    print(f"Generating Draftmancer format for {len(selected_sets)} selected sets with quantities: {pack_quantities}")
    print(f"Layout: {investigators_per_pack} investigators, {basic_weaknesses_per_pack} weaknesses, {player_cards_per_pack} player cards per pack, {player_card_packs_per_player} player card packs per player")
    if excluded_cards:
        print(f"Excluding {len(excluded_cards)} cards: {list(excluded_cards)}")
    arkham_cards = get_arkham_cards()

    if not arkham_cards:
        return render_template('draft_result.html', selected_sets=selected_sets, 
                             error="Unable to load card data")

    try:
        draftmancer_data = convert_to_draftmancer_format(arkham_cards, selected_sets, include_xp_cards)

        if "error" in draftmancer_data:
            return render_template('draft_result.html', selected_sets=selected_sets, 
                                 error=draftmancer_data["error"])

        # Generate cards for all three sheets with actual quantities and pack multipliers
        investigators_cards = generate_investigators_cards(draftmancer_data["selected_pack_codes"], pack_quantities, excluded_cards, taboo_modifications, unique_cards_only)
        basic_weaknesses_cards = generate_basic_weaknesses_cards(draftmancer_data["selected_pack_codes"], pack_quantities, excluded_cards, taboo_modifications, unique_cards_only)
        player_cards = generate_player_cards(draftmancer_data["selected_pack_codes"], pack_quantities, excluded_cards, taboo_modifications, unique_cards_only, include_xp_cards)
        
        # Add cards to include to appropriate lists and get custom cards
        try:
            investigators_cards, basic_weaknesses_cards, player_cards, custom_cards = add_cards_to_include_to_lists(
                cards_to_include, investigators_cards, basic_weaknesses_cards, player_cards, arkham_cards
            )
        except Exception as e:
            print(f"Error adding cards to include: {e}")
            custom_cards = []
        
        # Add custom cards to draftmancer data
        if custom_cards:
            draftmancer_data["cards"].extend(custom_cards)
            draftmancer_data["count"] += len(custom_cards)
        
        # Generate complete Draftmancer file content
        file_content = generate_draftmancer_file_content(
            draftmancer_data["cards"],
            investigators_cards,
            basic_weaknesses_cards,
            player_cards,
            selected_sets,
            investigators_per_pack,
            basic_weaknesses_per_pack,
            player_cards_per_pack,
            player_card_packs_per_player
        )
        
        # Generate filename with timestamp and new extension
        from datetime import datetime
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"arkham_draft_{timestamp}.draftmancer.txt"
        
        # Generate file content but don't save locally
        investigator_count = draftmancer_data['count']
        investigators_count = len(investigators_cards)
        basic_weaknesses_count = len(basic_weaknesses_cards)
        player_cards_count = len(player_cards)
        print(f"Generated Draftmancer file: {filename} with {investigator_count} custom cards, {investigators_count} investigators, {basic_weaknesses_count} basic weaknesses, and {player_cards_count} player cards")
        
        return render_template('draft_result.html', 
                             selected_sets=selected_sets,
                             card_count=investigator_count,
                             investigators_count=investigators_count,
                             basic_weaknesses_count=basic_weaknesses_count,
                             player_cards_count=player_cards_count,
                             filename=filename,
                             file_content=file_content)
    
    except Exception as e:
        print(f"Error generating Draftmancer file: {e}")
        return render_template('draft_result.html', selected_sets=selected_sets, 
                             error=f"Error generating draft: {str(e)}")

@app.route('/draft-now', methods=['POST'])
def draft_now():
    from flask import jsonify
    
    arkham_cards = get_arkham_cards()
    selected_sets = request.form.getlist('sets')
    
    # Get selected taboo list
    taboo_list_id = request.form.get('tabooList', '').strip()
    taboo_modifications = get_taboo_modifications(taboo_list_id)
    
    if taboo_modifications:
        forbidden_count = len([code for code, mods in taboo_modifications.items() 
                              if any('Forbidden' in mod.get('text', '') for mod in mods)])
        print(f"Applying taboo list {taboo_list_id}: excluding {forbidden_count} forbidden cards")
    
    # Check for cards to include first
    cards_to_include_text = request.form.get('cardsToInclude', '').strip()
    
    if not selected_sets and not cards_to_include_text:
        return jsonify({"error": "No sets selected and no cards to include specified"}), 400

    # Process pack quantities - get quantities for each selected pack
    pack_quantities = {}
    for pack_name in selected_sets:
        quantity_key = f'quantity_{pack_name}'
        quantity = int(request.form.get(quantity_key, 1))  # Default to 1 if not specified
        pack_quantities[pack_name] = quantity
    
    # Parse excluded cards
    excluded_cards_text = request.form.get('cardsToExclude', '').strip()
    excluded_cards = parse_excluded_cards(excluded_cards_text)
    
    # Parse cards to include (moved earlier for validation)
    try:
        cards_to_include = parse_cards_to_include(cards_to_include_text)
        if cards_to_include:
            print(f"Including {len(cards_to_include)} custom cards for immediate draft: {list(cards_to_include.keys())}")
    except Exception as e:
        print(f"Error parsing cards to include: {e}")
        cards_to_include = {}
    
    # Parse layout options
    investigators_per_pack = int(request.form.get('investigatorsPerPack', 3))
    basic_weaknesses_per_pack = int(request.form.get('basicWeaknessesPerPack', 3))
    player_cards_per_pack = int(request.form.get('playerCardsPerPack', 15))
    player_card_packs_per_player = int(request.form.get('playerCardPacksPerPlayer', 3))
    unique_cards_only = request.form.get('uniqueCardsOnly') == 'on'
    include_xp_cards = request.form.get('includeXpCards') == 'on'
    
    if unique_cards_only:
        print("Unique cards only setting enabled for immediate draft - limiting each card to appear at most once")
    if include_xp_cards:
        print("Include XP cards setting enabled for immediate draft - including all higher level cards in the draft pool")
    
    # Get all cards and convert to Draftmancer format
    print(f"Generating Draftmancer format for immediate draft with {len(selected_sets)} selected sets and quantities: {pack_quantities}")
    print(f"Layout: {investigators_per_pack} investigators, {basic_weaknesses_per_pack} weaknesses, {player_cards_per_pack} player cards per pack, {player_card_packs_per_player} player card packs per player")
    if excluded_cards:
        print(f"Excluding {len(excluded_cards)} cards: {list(excluded_cards)}")
    arkham_cards = get_arkham_cards()

    if not arkham_cards:
        return jsonify({"error": "Unable to load card data"}), 500

    draftmancer_data = convert_to_draftmancer_format(arkham_cards, selected_sets, include_xp_cards)

    if "error" in draftmancer_data:
        return jsonify({"error": draftmancer_data["error"]}), 500

    # Generate cards for all three sheets with actual quantities and pack multipliers
    investigators_cards = generate_investigators_cards(draftmancer_data["selected_pack_codes"], pack_quantities, excluded_cards, taboo_modifications, unique_cards_only)
    basic_weaknesses_cards = generate_basic_weaknesses_cards(draftmancer_data["selected_pack_codes"], pack_quantities, excluded_cards, taboo_modifications, unique_cards_only)
    player_cards = generate_player_cards(draftmancer_data["selected_pack_codes"], pack_quantities, excluded_cards, taboo_modifications, unique_cards_only, include_xp_cards)
    
    # Add cards to include to appropriate lists and get custom cards
    try:
        investigators_cards, basic_weaknesses_cards, player_cards, custom_cards = add_cards_to_include_to_lists(
            cards_to_include, investigators_cards, basic_weaknesses_cards, player_cards, arkham_cards, draftmancer_data["cards"]
        )
    except Exception as e:
        print(f"Error adding cards to include for immediate draft: {e}")
        custom_cards = []
    
    # Add custom cards to draftmancer data
    if custom_cards:
        draftmancer_data["cards"].extend(custom_cards)
        draftmancer_data["count"] += len(custom_cards)
    
    # Generate complete Draftmancer file content
    file_content = generate_draftmancer_file_content(
        draftmancer_data["cards"],
        investigators_cards,
        basic_weaknesses_cards,
        player_cards,
        selected_sets,
        investigators_per_pack,
        basic_weaknesses_per_pack,
        player_cards_per_pack,
        player_card_packs_per_player
    )
    
    # Return JSON data for immediate drafting
    investigators_count = len(investigators_cards)
    basic_weaknesses_count = len(basic_weaknesses_cards)
    
    # Calculate total quantity of player cards (sum of all quantities, not unique cards)
    player_cards_total_quantity = 0
    for card_entry in player_cards:
        # Extract quantity from entries like "3 Emergency Cache (AHCORE) 88"
        try:
            quantity = int(card_entry.split(' ', 1)[0])
            player_cards_total_quantity += quantity
        except (ValueError, IndexError):
            continue  # Skip malformed entries
    
    print(f"Generated Draftmancer content for immediate draft with {draftmancer_data['count']} custom cards, {investigators_count} investigators, {basic_weaknesses_count} basic weaknesses, and {player_cards_total_quantity} total player cards ({len(player_cards)} unique)")
    
    return jsonify({
        "cubeFile": file_content,
        "metadata": {
            "cardCount": draftmancer_data['count'],
            "investigatorsCount": investigators_count,
            "basicWeaknessesCount": basic_weaknesses_count,
            "playerCardsCount": player_cards_total_quantity,
            "selectedSets": selected_sets
        }
    })

@app.route('/get-draft-content', methods=['POST'])
def get_draft_content():
    """Return draft file content for client-side download."""
    from flask import jsonify
    
    selected_sets = request.form.getlist('sets')
    
    # Get selected taboo list
    taboo_list_id = request.form.get('tabooList', '').strip()
    taboo_modifications = get_taboo_modifications(taboo_list_id)
    
    if taboo_modifications:
        forbidden_count = len([code for code, mods in taboo_modifications.items() 
                              if any('Forbidden' in mod.get('text', '') for mod in mods)])
        print(f"Applying taboo list {taboo_list_id}: excluding {forbidden_count} forbidden cards")
    
    # Check for cards to include first
    cards_to_include_text = request.form.get('cardsToInclude', '').strip()
    
    if not selected_sets and not cards_to_include_text:
        return jsonify({"error": "No sets selected and no cards to include specified"}), 400
    
    # Process pack quantities
    pack_quantities = {}
    if selected_sets:
        for pack_name in selected_sets:
            quantity_key = f'quantity_{pack_name}'
            quantity = int(request.form.get(quantity_key, 1))
            pack_quantities[pack_name] = quantity
    
    # Parse excluded cards
    excluded_cards_text = request.form.get('cardsToExclude', '').strip()
    excluded_cards = parse_excluded_cards(excluded_cards_text)
    
    # Parse cards to include
    try:
        cards_to_include = parse_cards_to_include(cards_to_include_text)
    except Exception as e:
        print(f"Error parsing cards to include: {e}")
        cards_to_include = {}
    
    # Parse layout options
    investigators_per_pack = int(request.form.get('investigatorsPerPack', 3))
    basic_weaknesses_per_pack = int(request.form.get('basicWeaknessesPerPack', 3))
    player_cards_per_pack = int(request.form.get('playerCardsPerPack', 15))
    unique_cards_only = request.form.get('uniqueCardsOnly') == 'on'
    include_xp_cards = request.form.get('includeXpCards') == 'on'
    
    if unique_cards_only:
        print("Unique cards only setting enabled for draft content - limiting each card to appear at most once")
    if include_xp_cards:
        print("Include XP cards setting enabled for draft content - including all higher level cards in the draft pool")
    
    try:
        arkham_cards = get_arkham_cards()
        
        if not arkham_cards:
            return jsonify({"error": "Unable to load card data"}), 500
        
        # Convert to draftmancer format (only if we have selected sets)
        if selected_sets:
            draftmancer_data = convert_to_draftmancer_format(arkham_cards, selected_sets, include_xp_cards)
            if "error" in draftmancer_data:
                return jsonify({"error": draftmancer_data["error"]}), 500
        else:
            # No selected sets, create empty draftmancer data structure
            draftmancer_data = {
                "cards": [],
                "count": 0,
                "selected_packs": [],
                "selected_pack_codes": set(),
                "filtered_cards": []
            }
        
        # Generate cards for all three sheets
        investigators_cards = generate_investigators_cards(draftmancer_data["selected_pack_codes"], pack_quantities, excluded_cards, taboo_modifications, unique_cards_only)
        basic_weaknesses_cards = generate_basic_weaknesses_cards(draftmancer_data["selected_pack_codes"], pack_quantities, excluded_cards, taboo_modifications, unique_cards_only)
        player_cards = generate_player_cards(draftmancer_data["selected_pack_codes"], pack_quantities, excluded_cards, taboo_modifications, unique_cards_only, include_xp_cards)
        
        # Add cards to include to appropriate lists and get custom cards
        try:
            investigators_cards, basic_weaknesses_cards, player_cards, custom_cards = add_cards_to_include_to_lists(
                cards_to_include, investigators_cards, basic_weaknesses_cards, player_cards, arkham_cards, draftmancer_data["cards"]
            )
        except Exception as e:
            print(f"Error adding cards to include: {e}")
            custom_cards = []
        
        # Add custom cards to draftmancer data
        if custom_cards:
            draftmancer_data["cards"].extend(custom_cards)
            draftmancer_data["count"] += len(custom_cards)
        
        # Generate complete Draftmancer file content
        player_card_packs_per_player = int(request.form.get('playerCardPacksPerPlayer', 3))
        file_content = generate_draftmancer_file_content(
            draftmancer_data["cards"],
            investigators_cards,
            basic_weaknesses_cards,
            player_cards,
            selected_sets,
            investigators_per_pack,
            basic_weaknesses_per_pack,
            player_cards_per_pack,
            player_card_packs_per_player
        )
        
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"arkham_draft_{timestamp}.draftmancer.txt"
        
        return jsonify({
            "success": True,
            "filename": filename,
            "content": file_content
        })
        
    except Exception as e:
        print(f"Error generating draft content: {e}")
        return jsonify({"error": f"Error generating draft: {str(e)}"}), 500

@app.route('/favicon.ico')
def favicon():
    """Serve the favicon."""
    from flask import send_from_directory
    return send_from_directory('static', 'favicon.ico', mimetype='image/vnd.microsoft.icon')

if __name__ == '__main__':
    app.run(debug=True)